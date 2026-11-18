#!/usr/bin/env python3
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import signal
import subprocess
import sys
import time

BASE = 'b1b837744410437694bd5b4f1002aed97ecb8bda'
FINAL = 'cda67a0f977b45124d08d4ebaba6877f514bde5a'
MODE = os.environ.get('TERSUS_PAIR_MODE', 'preparation-only')
sides = {}
BASE_CABAL_GENERATED_SHA256 = '94d48cb8eed32119a744d543bbe604eec1591f2aacf3db7d66a44d91fdaf1ce2'
repo = Path.cwd()
out = Path(os.environ['RUNNER_TEMP']) / 'tersus-final-pair'
out.mkdir()
cpus = sorted(os.sched_getaffinity(0))[:4]
deadline = time.monotonic() + 19800
record = {'baseline': BASE, 'final': FINAL, 'mode': MODE, 'status': 'running', 'cpu_lane': cpus,
          'suite_workers': 4, 'suite_parent_rts': '-N2', 'commands': [],
          'cold_cache_policy': 'empty per version; no preparation entries copied',
          'suite_cache_policy': 'each version reuses only its own measured cold cache',
          'memory_scope': 'runner/cgroup limit; suite admission budget is its unchanged production harness',
          'maxrss_scope': 'GNU time: largest process, not simultaneous process-tree sum',
          'tree_rss_scope': 'existing ci_resources.py samples: summed RSS includes shared pages'}
resources = out / 'ci_resources.py'
resources.write_bytes(subprocess.check_output(['git', 'show', FINAL + ':tersus/dev/ci_resources.py']))

def save():
    (out / 'result.json').write_text(json.dumps(record, indent=2) + '\n')

def source_snapshot(side, phase):
    root = sides[side][0].parent
    revision = record[side]['revision']
    prefix = side + '-' + phase
    evidence = {'phase': phase, 'revision': revision, 'inspection_errors': []}
    record[side].setdefault('source_snapshots', []).append(evidence)
    try:
        def git(*args):
            return subprocess.check_output(['git', *args], cwd=root)
        (out / (prefix + '.name-status')).write_bytes(git('diff', '--name-status', revision, '--'))
        (out / (prefix + '.patch')).write_bytes(git('diff', '--binary', revision, '--'))
        changed = git('diff', '--name-only', '-z', revision, '--').decode().split('\0')
        changed = [path for path in changed if path]
        evidence['changed_paths'] = changed
        files = git('ls-files', '-z').decode().split('\0')
        manifest = {}
        for path in filter(None, files):
            try:
                contents = (root / path).read_bytes()
                manifest[path] = {'bytes': len(contents), 'sha256': hashlib.sha256(contents).hexdigest()}
            except OSError as error:
                manifest[path] = {'error': str(error)}
                evidence['inspection_errors'].append(path + ': ' + str(error))
        (out / (prefix + '.tracked-hashes.json')).write_text(json.dumps(manifest, indent=2) + '\n')
        pin = 'tersus/bootstrap/emitter.sha256'
        verified = record[side].get('verified_gen_pin_sha256')
        permitted = side == 'final' and verified and manifest.get(pin, {}).get('sha256') == verified
        allowed = {pin} if permitted else set()
        cabal = 'tersus/tersus.cabal'
        if side == 'baseline' and manifest.get(cabal, {}).get('sha256') == BASE_CABAL_GENERATED_SHA256:
            allowed.add(cabal)
            evidence['baseline_qualification'] = 'b1 plus exact normal hpack test-suite TestClosures discovery, already imported and executed'
        evidence['violations'] = [path for path in changed if path not in allowed]
        frozen = record[side].get('frozen_input_hashes')
        if frozen is not None:
            evidence['frozen_input_drift'] = [path for path in sorted(set(frozen) | set(manifest))
                                             if frozen.get(path) != manifest.get(path)]
            evidence['violations'] = sorted(set(evidence['violations']) | set(evidence['frozen_input_drift']))
        evidence['manifest_file'] = prefix + '.tracked-hashes.json'
    except Exception as error:
        evidence['inspection_errors'].append(str(error))
    save()
    return evidence

def check_source(side, phase):
    evidence = source_snapshot(side, phase)
    if evidence.get('violations') or evidence['inspection_errors']:
        raise RuntimeError(side + ' source drift at ' + phase + ': ' + str(evidence))


def run(label, argv, cwd, env, bound=1800):
    entry = {'label': label, 'argv': argv, 'cwd': str(cwd),
             'environment': {key: env.get(key) for key in ['XDG_CACHE_HOME', 'TMPDIR', 'GHCRTS',
                 'TERSUS_TEST_RTS_STATS', 'TERSUS_SEED_FILE', 'TERSUS_FRONTEND_SEED_FILE',
                 'TERSUS_PARSER_SEED_FILE', 'TERSUS_TEST_APPROVED_BUILD_IDENTITY', 'TERSUS_EMITTER_BUILD_MANIFEST']},
             'profile_record': str(out / 'final-profile-after.stdout') if label.startswith('final-') else 'baseline unchanged ordinary build',
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    record['commands'].append(entry)
    save()
    left = min(bound, int(deadline - time.monotonic()))
    if left <= 0:
        raise RuntimeError('pair deadline exhausted before ' + label)
    command = ['timeout', '--signal=TERM', '--kill-after=30s', str(left),
               sys.executable, str(resources), '--', '/usr/bin/time',
               '-f', '{"wall_s":%e,"user_s":%U,"sys_s":%S,"maxrss_largest_process_kib":%M,"exit":%x}',
               '-o', str(out / (label + '.time.json')), 'taskset', '-c', ','.join(map(str, cpus))] + argv
    start = time.monotonic()
    with (out / (label + '.stdout')).open('wb') as stdout, (out / (label + '.stderr')).open('wb') as stderr:
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            code = child.wait(timeout=left + 40)
        except BaseException:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=30)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            raise
    entry.update(exit=code, elapsed_controller_s=time.monotonic() - start,
                 ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save()
    for side, (package, _, _) in sides.items():
        if package == cwd:
            source_snapshot(side, label + '-command-exit')
    metrics = out / (label + '.time.json')
    if metrics.exists():
        raw_metrics = metrics.read_text()
        entry['time_raw'] = raw_metrics
        try:
            entry['time'] = json.loads(next(line for line in raw_metrics.splitlines() if line.startswith('{')))
        except (StopIteration, ValueError) as error:
            entry['metrics_error'] = str(error)
    sampled = []
    for line in (out / (label + '.stderr')).read_text().splitlines():
        if line.startswith('[CI_RESOURCE] '):
            sampled.append(json.loads(line[len('[CI_RESOURCE] '):]))
    trees = [sample.get('process_tree', {}) for sample in sampled]
    entry['sampled_process_tree_peak_rss_kib'] = max((tree.get('rss_sum_kib', 0) for tree in trees), default=0)
    entry['sampled_process_tree_max_processes'] = max((tree.get('count', 0) for tree in trees), default=0)
    entry['resource_start_finish'] = [sample for sample in sampled if sample.get('phase') in ['start', 'finish']]
    save()
    if code:
        raise RuntimeError(label + ' failed or timed out, exit ' + str(code))
    if 'time' not in entry:
        raise RuntimeError(label + ' completed without valid timing metrics')
    return entry

def inventory(cache):
    root = cache / 'tersus'
    return ([{'name': p.name, 'bytes': p.stat().st_size if p.is_file() else None}
             for p in sorted(root.iterdir())] if root.exists() else [])

def memory_ready(phase):
    mem_kib = int(re.search(r'^MemAvailable:\s+(\d+)', Path('/proc/meminfo').read_text(), re.M).group(1))
    group = observer['cgroup_directory']()
    memory_max = observer['read'](group / 'memory.max') if group else None
    memory_current = observer['read'](group / 'memory.current') if group else None
    if memory_max and memory_max.isdigit() and memory_current and memory_current.isdigit():
        mem_kib = min(mem_kib, (int(memory_max) - int(memory_current)) // 1024)
    record.setdefault('memory_checks', []).append({'phase': phase, 'available_kib': mem_kib,
        'cgroup_path': str(group), 'max': memory_max, 'current': memory_current})
    save()
    if len(cpus) < 2 or mem_kib < 12 * 1024 * 1024:
        raise RuntimeError(phase + ': runner cannot safely fit the unchanged suite; need >=2 CPUs and >=12 GiB available memory')

try:
    if MODE not in ['preparation-only', 'measure']:
        raise RuntimeError('unknown pair mode: ' + MODE)
    observer = runpy.run_path(str(resources), run_name='pair_resource_observer')
    memory_ready('before-setup')
    if subprocess.check_output(['git', 'merge-base', BASE, FINAL], text=True).strip() != BASE:
        raise RuntimeError('frozen baseline is not the final merge-base')
    env = dict(os.environ)
    env.pop('TERSUS_TEST_APPROVED_BUILD_IDENTITY', None)
    env.pop('TERSUS_EMITTER_BUILD_MANIFEST', None)
    env.update(GHCRTS='-A16m', TERSUS_TEST_RTS_STATS='1')
    run('normal-toolchain-setup', ['stack', 'setup'], repo / 'tersus', env, 1800)
    version = subprocess.check_output(['stack', 'exec', '--', 'ghc', '--numeric-version'], cwd=repo / 'tersus', env=env, text=True).strip()
    record['actual_ghc_version'] = version
    if version != '9.6.5':
        raise RuntimeError('normal Stack resolver did not select GHC 9.6.5')
    for side, revision in [('baseline', BASE), ('final', FINAL)]:
        work = out / side
        subprocess.run(['git', 'worktree', 'add', '--detach', str(work), revision], check=True)
        root = work / 'tersus'
        prep = out / (side + '-preparation-cache')
        measured = out / (side + '-measured-cache')
        temporary = out / (side + '-measured-tmp')
        for directory in [prep, measured, temporary, out / (side + '-preparation-tmp')]:
            directory.mkdir()
        side_env = dict(env, XDG_CACHE_HOME=str(prep), TMPDIR=str(out / (side + '-preparation-tmp')))
        sides[side] = (root, side_env, measured)
        record[side] = {'revision': revision, 'tree': subprocess.check_output(['git', 'rev-parse', revision + '^{tree}'], text=True).strip()}
        check_source(side, 'checkout')
        seeds = {}
        for stage in ['emitter', 'frontend', 'parser']:
            pin = (root / ('bootstrap/' + stage + '.sha256')).read_text().split()
            digest = pin[0]
            asset = out / (digest + '-' + stage + '.ll')
            if not asset.exists():
                subprocess.run(['curl', '--fail', '--location', '--max-time', '300',
                    'https://github.com/weirdev/tersus/releases/download/bootstrap-' + digest[:12] + '/' + stage + '.ll',
                    '-o', str(asset)], check=True)
            if hashlib.sha256(asset.read_bytes()).hexdigest() != digest:
                raise RuntimeError(side + ' ' + stage + ' seed digest mismatch')
            side_env['TERSUS_' + ('SEED_FILE' if stage == 'emitter' else stage.upper() + '_SEED_FILE')] = str(asset)
            seeds[stage] = {'pin': pin, 'bytes': asset.stat().st_size, 'sha256': digest}
        record[side]['seeds'] = seeds
        run(side + '-build', ['stack', 'build', '--test', '--no-run-tests'], root, side_env, 2400)
        check_source(side, 'after-build')
        if side == 'final':
            run('final-profile-before', ['stack', 'run', 'emitter-seed', '--', 'profile'], root, side_env)
            certified = out / 'final-certified.pin'
            run('final-gen-preparation', ['stack', 'run', 'emitter-seed', '--', 'certify', str(out / 'final-certified.ll'), str(certified), '+RTS', '-qg', '-RTS'], root, side_env, 2400)
            fields = certified.read_text().split()
            if len(fields) != 2 or fields[0] != seeds['emitter']['sha256']:
                raise RuntimeError('normal GEN did not certify the final published seed')
            record[side]['verified_gen_pin_sha256'] = hashlib.sha256(certified.read_bytes()).hexdigest()
            (root / 'bootstrap/emitter.sha256').write_bytes(certified.read_bytes())
            check_source(side, 'after-GEN-pin')
            run('final-metadata-build', ['stack', 'build', '--test', '--no-run-tests'], root, side_env, 1200)
            run('final-profile-after', ['stack', 'run', 'emitter-seed', '--', 'profile'], root, side_env)
            if (out / 'final-profile-before.stdout').read_bytes() != (out / 'final-profile-after.stdout').read_bytes():
                raise RuntimeError('metadata-only GEN pin changed actual common-library profile/construction')
            record['final']['measured_pin'] = fields
        check_source(side, 'after-preparation')
        if side == 'baseline':
            cabal_digest = hashlib.sha256((root / 'tersus.cabal').read_bytes()).hexdigest()
            if cabal_digest != BASE_CABAL_GENERATED_SHA256:
                raise RuntimeError('baseline normal build did not reproduce the exact qualified Cabal metadata')
            record[side]['baseline_qualification'] = {'base_revision': BASE,
                'generated_cabal_sha256': cabal_digest,
                'change': 'test-suite other-modules adds already imported/executed TestClosures only'}
        snapshot = record[side]['source_snapshots'][-1]
        record[side]['frozen_input_hashes'] = json.loads((out / snapshot['manifest_file']).read_text())
        record[side]['preparation_cache'] = inventory(prep)
        side_env.update(XDG_CACHE_HOME=str(measured), TMPDIR=str(temporary))
        if list(measured.iterdir()) or list(temporary.iterdir()):
            raise RuntimeError('measured cold cache or temporary directory is not empty')
        sides[side] = (root, side_env, measured)
        save()
    for side in sides:
        check_source(side, 'before-measurement')
    if MODE == 'preparation-only':
        record['status'] = 'preparation_clean'
        save()
        print('Preparation clean for both frozen inputs; no cold or suite was run')
        sys.exit(0)
    for side in ['baseline', 'final']:
        root, side_env, cache = sides[side]
        revision = record[side]['revision']
        record[side]['cold_cache_before'] = inventory(cache)
        memory_ready(side + '-before-cold')
        run(side + '-cold', ['stack', 'run', 'tersus-exe', '--', 'llvm', 'examples/basics.tersus', '+RTS', '-qg', '-RTS'], root, side_env, 1800)
        check_source(side, 'after-cold')
        record[side]['cold_cache_after'] = inventory(cache)
        emitters = [x['name'] for x in record[side]['cold_cache_after'] if x['name'].startswith('emitter-')]
        record[side]['source_emitter_cache_entries'] = emitters
        prepared_emit_results = []
        for entry in record[side]['cold_cache_after']:
            if entry['name'].startswith('prepared-') and not entry['name'].endswith('.lock'):
                with (cache / 'tersus' / entry['name']).open('rb') as payload:
                    if any(re.match(rb'struct "[^"]*EmitResult" ', line) for line in payload):
                        prepared_emit_results.append(entry['name'])
        record[side]['prepared_emitter_payloads'] = prepared_emit_results
        if side == 'final' and (emitters or prepared_emit_results or not any(x['name'].startswith('seed-') for x in record[side]['cold_cache_after'])):
            raise RuntimeError('final ordinary CLI did not use the genuine known published route without SOURCE emitter preparation')
        memory_ready(side + '-before-suite')
        run(side + '-suite', ['stack', 'test', '--test-arguments=-j 4 +RTS -N2 -qg -RTS'], root, side_env, 6600)
        check_source(side, 'after-suite')
        text = (out / (side + '-suite.stdout')).read_text() + (out / (side + '-suite.stderr')).read_text()
        summaries = re.findall(r'Summary:\s*(\d+) passed,\s*(\d+) failed', text)
        if not summaries or int(summaries[-1][0]) == 0 or int(summaries[-1][1]) != 0 or '[CRASH]' in text or '[FAIL]' in text:
            raise RuntimeError(side + ' suite has missing or failed test results')
        record[side]['suite_summary'] = list(map(int, summaries[-1]))
        record[side]['suite_cache_after'] = inventory(cache)
        save()
    metrics = {x['label']: x['time'] for x in record['commands'] if 'time' in x}
    record['wall_ratios'] = {phase: metrics['final-' + phase]['wall_s'] / metrics['baseline-' + phase]['wall_s'] for phase in ['cold', 'suite']}
    record['cpu_ratios'] = {phase: (metrics['final-' + phase]['user_s'] + metrics['final-' + phase]['sys_s']) / (metrics['baseline-' + phase]['user_s'] + metrics['baseline-' + phase]['sys_s']) for phase in ['cold', 'suite']}
    record['status'] = 'passed' if all(value <= 1.25 for value in record['wall_ratios'].values()) else 'budget_failed'
    save()
    print(json.dumps({'status': record['status'], 'wall_ratios': record['wall_ratios'], 'cpu_ratios': record['cpu_ratios']}))
    if record['status'] != 'passed':
        sys.exit(1)
except Exception as error:
    record.update(status='failed', error=str(error))
    save()
    raise
finally:
    final_snapshots = [source_snapshot(side, 'all-exits') for side in sides]
    if any(s.get('violations') or s['inspection_errors'] for s in final_snapshots):
        if record['status'] in ['passed', 'preparation_clean']:
            record.update(status='failed', error='source drift or incomplete inspection on exit')
            save()
            raise RuntimeError(record['error'])
