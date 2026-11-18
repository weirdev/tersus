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
resource_source = subprocess.check_output(['git', 'show', FINAL + ':tersus/dev/ci_resources.py']).decode()
resource_original_sha256 = hashlib.sha256(resource_source.encode()).hexdigest()
resource_handler = '        nonlocal cancelled\n        cancelled = signum\n'
if resource_source.count(resource_handler) != 1:
    raise RuntimeError('unrecognized resource observer cancellation handler')
resource_source = resource_source.replace(resource_handler,
    '        nonlocal cancelled\n        if cancelled is not None:\n            return\n        cancelled = signum\n', 1)
resources.write_text(resource_source)
record['resource_observer_qualification'] = {'change': 'one-shot cancellation in temporary copy; repeated TERM cannot interrupt owned-child cleanup',
    'original_sha256': resource_original_sha256, 'temporary_sha256': hashlib.sha256(resource_source.encode()).hexdigest()}

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
        generated = record[side].get('generated_input_hashes')
        if generated is not None:
            if manifest.get(cabal) == generated.get(cabal):
                allowed.add(cabal)
            evidence['generated_input_drift'] = [path for path in sorted(set(generated) | set(manifest))
                if path != pin and generated.get(path) != manifest.get(path)]
        evidence['violations'] = sorted(set(path for path in changed if path not in allowed)
                                        | set(evidence.get('generated_input_drift', [])))
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


def semantic_cabal(text):
    result, component, declared_paths = [], None, False
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        if line == 'library' or line.startswith(('executable ', 'test-suite ')):
            component, declared_paths = line, False
        if line.strip() == 'Paths_tersus':
            declared_paths = True
        if line.strip() == 'autogen-modules:':
            if not declared_paths or index + 1 >= len(lines) or lines[index + 1].strip() != 'Paths_tersus':
                raise RuntimeError('unrecognized generated module classification in ' + str(component))
            if index + 2 < len(lines) and lines[index + 2].startswith('      '):
                raise RuntimeError('additional generated module classification')
            index += 2
            continue
        if not line.startswith('--'):
            result.append(line)
        index += 1
    return result


def accept_generation(side):
    root = sides[side][0].parent
    revision = record[side]['revision']
    evidence = source_snapshot(side, 'normal-generation')
    if evidence['inspection_errors'] or any(p != 'tersus/tersus.cabal' for p in evidence['changed_paths']):
        raise RuntimeError('generation changed non-Cabal inputs: ' + str(evidence))
    old = subprocess.check_output(['git', 'show', revision + ':tersus/tersus.cabal'], cwd=root, text=True)
    new = (root / 'tersus/tersus.cabal').read_text()
    old_lines, new_lines = semantic_cabal(old), semantic_cabal(new)
    if side == 'baseline' and '      TestClosures' not in old_lines:
        runner = (root / 'tersus/test/TestTersus.hs').read_text()
        if not (root / 'tersus/test/TestClosures.hs').is_file() or 'import TestClosures' not in runner or ', testClosures' not in runner:
            raise RuntimeError('new test module was not already imported and registered')
        position = old_lines.index('test-suite tersus-test')
        anchor = old_lines.index('      TestBytes', position)
        old_lines.insert(anchor + 1, '      TestClosures')
    comparison = {'equal': old_lines == new_lines, 'original': old_lines, 'generated': new_lines,
                  'checks': 'unchanged stanzas, flags, dependencies, module exposure and test selection; existing Paths_tersus autogen classification only'}
    (out / (side + '-generation-semantics.json')).write_text(json.dumps(comparison, indent=2) + '\n')
    if not comparison['equal']:
        raise RuntimeError(side + ' normal generation changed semantic configuration')
    manifest = json.loads((out / evidence['manifest_file']).read_text())
    record[side]['generated_input_hashes'] = manifest
    record[side]['generation_qualification'] = {'source': revision, 'cabal': manifest['tersus/tersus.cabal'],
        'generator': record['toolchain'], 'semantic_configuration_equal': True}
    check_source(side, 'generated-inputs-frozen')


class Terminated(Exception):
    def __init__(self, signum):
        self.signum = signum
        super().__init__('controller received signal ' + str(signum))


pending_signal = None
deferring_signal = False


def on_signal(signum, _frame):
    global pending_signal
    if pending_signal is None:
        pending_signal = signum
        if not deferring_signal:
            raise Terminated(signum)


def run(label, argv, cwd, env, bound=1800):
    global deferring_signal
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
    primary_error = None
    child, code = None, None
    entry['bound_s'] = left
    print('[PAIR_START] ' + json.dumps({'label': label, 'argv': argv, 'bound_s': left,
          'started_utc': entry['started_utc']}), flush=True)
    try:
        with (out / (label + '.stdout')).open('wb') as stdout, (out / (label + '.stderr')).open('wb') as stderr:
            deferring_signal = True
            try:
                child = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
                entry.update(owned_child_pid=child.pid, owned_child_pgid=child.pid)
            finally:
                deferring_signal = False
            save()
            print('[PAIR_CHILD] ' + json.dumps({'label': label, 'owned_child_pid': child.pid}), flush=True)
            if pending_signal is not None:
                raise Terminated(pending_signal)
            try:
                code = child.wait(timeout=left + 40)
            finally:
                deferring_signal = True
    except BaseException as error:
        deferring_signal = True
        primary_error = error
        entry['primary_error'] = str(error)
        entry['interrupted'] = True
        if pending_signal is not None:
            entry['controller_signal'] = pending_signal
        save()
        if child is not None:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=30)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired as cleanup_error:
                    entry['cleanup_error'] = str(cleanup_error)
            code = child.returncode
    entry.update(exit=code, elapsed_controller_s=time.monotonic() - start,
                 ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save()
    print('[PAIR_COMMAND_END] ' + json.dumps({'label': label, 'exit': code,
          'elapsed_s': entry['elapsed_controller_s'], 'primary_error': entry.get('primary_error')}), flush=True)
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
    stderr_path = out / (label + '.stderr')
    for line in stderr_path.read_text(errors='replace').splitlines() if stderr_path.exists() else []:
        if line.startswith('[CI_RESOURCE] '):
            try:
                sampled.append(json.loads(line[len('[CI_RESOURCE] '):]))
            except ValueError as error:
                entry.setdefault('resource_diagnostics_errors', []).append(str(error))
    trees = [sample.get('process_tree', {}) for sample in sampled]
    entry['sampled_process_tree_peak_rss_kib'] = max((tree.get('rss_sum_kib', 0) for tree in trees), default=0)
    entry['sampled_process_tree_max_processes'] = max((tree.get('count', 0) for tree in trees), default=0)
    entry['resource_start_finish'] = [sample for sample in sampled if sample.get('phase') in ['start', 'finish']]
    save()
    print('[PAIR_STATUS] ' + json.dumps({'label': label, 'exit': code, 'time': entry.get('time'),
          'metrics_error': entry.get('metrics_error'), 'controller_signal': pending_signal,
          'primary_error': entry.get('primary_error')}), flush=True)
    deferring_signal = False
    if primary_error is not None:
        raise primary_error
    if pending_signal is not None:
        raise Terminated(pending_signal)
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

signal_handlers = {sig: signal.signal(sig, on_signal) for sig in [signal.SIGTERM, signal.SIGINT]}
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
    stack_version = subprocess.check_output(['stack', '--numeric-version'], env=env, text=True).strip()
    hpack_version = subprocess.check_output(['stack', '--hpack-numeric-version'], env=env, text=True).strip()
    record['toolchain'] = {'stack': stack_version, 'bundled_hpack': hpack_version, 'compiler': '9.6.5'}
    if (stack_version, hpack_version) != ('3.11.1', '0.39.6'):
        raise RuntimeError('the fixed normal Stack/Hpack generator is not selected')
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
        run(side + '-normal-generation', ['stack', '--hpack-force', 'build', '--dry-run', '--test', '--no-run-tests'], root, side_env, 1200)
        accept_generation(side)
    for side in ['baseline', 'final']:
        root, side_env, measured = sides[side]
        prep = Path(side_env['XDG_CACHE_HOME'])
        temporary = out / (side + '-measured-tmp')
        seeds = record[side]['seeds']
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
    if isinstance(error, Terminated):
        record['controller_signal'] = error.signum
    save()
    print('[PAIR_FAILED] ' + json.dumps({'error': str(error), 'signal': record.get('controller_signal'),
          'active_command': record['commands'][-1] if record['commands'] else None}), flush=True)
    if isinstance(error, Terminated):
        sys.exit(128 + error.signum)
    raise
finally:
    final_snapshots = [source_snapshot(side, 'all-exits') for side in sides]
    if any(s.get('violations') or s['inspection_errors'] for s in final_snapshots):
        if record['status'] in ['passed', 'preparation_clean']:
            record.update(status='failed', error='source drift or incomplete inspection on exit')
            save()
            raise RuntimeError(record['error'])
