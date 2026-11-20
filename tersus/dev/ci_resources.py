#!/usr/bin/env python3
import json
import os
import pathlib
import signal
import subprocess
import sys
import threading
import time


def read(path):
    try:
        return pathlib.Path(path).read_text().strip()
    except (OSError, UnicodeError):
        return None


def cgroup_directory():
    groups = read('/proc/self/cgroup') or ''
    mounts = read('/proc/self/mountinfo') or ''
    for group in groups.splitlines():
        fields = group.split(':', 2)
        if len(fields) != 3 or fields[:2] != ['0', '']:
            continue
        location = fields[2]
        for mount in mounts.splitlines():
            left, _, right = mount.partition(' - ')
            fields = left.split()
            if not right.startswith('cgroup2 ') or len(fields) < 5:
                continue
            root = pathlib.PurePosixPath(fields[3].replace('\\040', ' '))
            target = pathlib.Path(fields[4].replace('\\040', ' '))
            try:
                relative = pathlib.PurePosixPath(location).relative_to(root)
            except ValueError:
                if location != '/':
                    continue
                relative = pathlib.PurePosixPath('.')
            candidate = target / relative
            if (candidate / 'cgroup.procs').exists():
                return candidate
    return None


def process_tree(root):
    processes = {}
    inspected = 0
    truncated = False
    try:
        with os.scandir('/proc') as entries:
            for entry in entries:
                if not entry.name.isdecimal():
                    continue
                if inspected >= 2048:
                    truncated = True
                    break
                inspected += 1
                text = read(entry.path + '/stat')
                if not text:
                    continue
                end = text.rfind(')')
                fields = text[end + 2:].split()
                try:
                    pid = int(entry.name)
                    commands = (read(entry.path + '/cmdline') or '').split('\0')
                    group = commands[1] if '--child' in commands and len(commands) > 1 and commands[1].startswith('test') else None
                    processes[pid] = {'pid': pid, 'ppid': int(fields[1]), 'state': fields[0],
                                      'name': text[text.find('(') + 1:end], 'group': group,
                                      'rss_kib': int(fields[21]) * os.sysconf('SC_PAGE_SIZE') // 1024}
                except (ValueError, IndexError):
                    continue
    except OSError:
        return {'unavailable': True, 'inspected': inspected}
    if root not in processes:
        return {'incomplete': True, 'root_missing': True, 'inspected': inspected, 'truncated': truncated}
    selected = {root}
    while True:
        added = {pid for pid, info in processes.items() if info['ppid'] in selected} - selected
        if not added:
            break
        selected.update(added)
    rows = [processes[pid] for pid in selected]
    return {'count': len(rows), 'inspected': inspected, 'truncated': truncated,
            'rss_sum_kib': sum(row['rss_kib'] for row in rows),
            'rss_sum_includes_shared_pages': True,
            'largest': sorted(rows, key=lambda row: row['rss_kib'], reverse=True)[:8]}


def snapshot(group, phase):
    hardware = {'phase': phase, 'unix': time.time(), 'pid': os.getpid()}
    try:
        hardware['affinity'] = sorted(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        hardware['affinity'] = None
    hardware['cgroup_path'] = str(group) if group else None
    hardware['cgroup_scope'] = 'current process cgroup; may include unrelated processes'
    for name in ['cpu.max', 'cpu.stat', 'cpu.pressure', 'memory.max', 'memory.current',
                 'memory.peak', 'memory.swap.max', 'memory.swap.current', 'memory.events',
                 'memory.events.local', 'memory.pressure', 'io.pressure']:
        hardware[name] = read(group / name) if group else None
    meminfo = read('/proc/meminfo') or ''
    hardware['meminfo'] = '\n'.join(line for line in meminfo.splitlines()
                                   if line.split(':', 1)[0] in ['MemAvailable', 'SwapTotal', 'SwapFree'])
    hardware['host_cpu_pressure'] = read('/proc/pressure/cpu')
    hardware['host_memory_pressure'] = read('/proc/pressure/memory')
    hardware['process_tree'] = process_tree(os.getpid())
    print('[CI_RESOURCE] ' + json.dumps(hardware, sort_keys=True), file=sys.stderr, flush=True)


def telemetry(phase):
    try:
        snapshot(cgroup_directory(), phase)
    except Exception as error:
        try:
            print('[CI_RESOURCE_UNAVAILABLE] ' + type(error).__name__, file=sys.stderr, flush=True)
        except Exception:
            pass


class Cancelled(Exception):
    pass


def cancel_child(child, signum):
    try:
        os.killpg(child.pid, signum)
    except ProcessLookupError:
        pass
    try:
        child.wait(timeout=1)
    except subprocess.TimeoutExpired:
        pass
    finally:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait()


def main():
    arguments = sys.argv[1:]
    if not arguments:
        telemetry('snapshot')
        return 0
    if arguments[0] != '--' or len(arguments) == 1:
        raise SystemExit('usage: ci_resources.py [-- command args...]')
    stop = threading.Event()
    child = None
    worker = None
    cancelled = None

    def on_signal(signum, _frame):
        nonlocal cancelled
        cancelled = signum
        if child is not None:
            raise Cancelled()

    handlers = {signum: signal.signal(signum, on_signal) for signum in [signal.SIGTERM, signal.SIGINT]}
    try:
        telemetry('start')
        child = subprocess.Popen(arguments[1:], start_new_session=True)
        if cancelled is not None:
            raise Cancelled()

        def sample():
            while not stop.wait(5):
                if child.poll() is not None:
                    return
                telemetry('running')

        try:
            monitor = threading.Thread(target=sample, daemon=True)
            monitor.start()
            worker = monitor
        except (RuntimeError, MemoryError):
            telemetry('sampler-unavailable')
        code = child.wait()
        return code if code >= 0 else 128 - code
    except (Cancelled, KeyboardInterrupt):
        if cancelled is None:
            cancelled = signal.SIGINT
        for signum in handlers:
            signal.signal(signum, signal.SIG_IGN)
        if child is not None:
            cancel_child(child, cancelled)
        return 128 + cancelled
    finally:
        stop.set()
        if worker is not None:
            worker.join(timeout=1)
        telemetry('finish')
        for signum, handler in handlers.items():
            signal.signal(signum, handler)


if __name__ == '__main__':
    raise SystemExit(main())
