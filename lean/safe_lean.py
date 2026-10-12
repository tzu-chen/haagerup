"""Elaborate one Lean file with Lake's module setup and the desktop resource guard.

Usage from the repository root:
    python lean/safe_lean.py lean/HaagerupIzumi/Analytic/GammaIntegral.lean
    python lean/safe_lean.py --build lean/HaagerupIzumi/Analytic/GammaIntegral.lean

Additional arguments are passed to Lean, e.g. `-o /absolute/path/Module.olean`.
The --build mode registers genuine Lake artifacts and traces for one source;
it accepts no extra arguments. Both modes require already-built dependencies.
Build mode first checks those dependencies with --no-build and then requests
only the selected module's leanArts target, never the whole library. Build
project sources in dependency order and do not edit prerequisites during a run.
Modern `module` headers let Lake select necessary import artifacts rather than
loading every private part. Do not use raw Lean without its generated setup.

Observed peak group RSS for the gamma modules is approximately 2.5 GiB;
that is not an allocation estimate for other modules. The installed shared
research-safe-run guard and ~/.codex/AGENTS.md define current resource
policy, including preflight and the small runtime-helper build. Queue jobs
must declare a reviewed memory estimate; an exhausted budget requires
review before another attempt.
"""

from pathlib import Path
import hashlib
import os
import re
import resource
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / 'lean'
GIB = 1024 ** 3
RESOURCE_GUARD = Path.home() / '.local/bin/research-safe-run'


def main():
    arguments = sys.argv[1:]
    guarded = bool(arguments and arguments[0] == '--guarded')
    if guarded:
        arguments = arguments[1:]
    build = bool(arguments and arguments[0] == '--build')
    if build:
        arguments = arguments[1:]
    if not arguments:
        sys.exit(__doc__)
    if build and len(arguments) != 1:
        sys.exit('--build accepts one source file and no extra compiler or Lake arguments')
    source = Path(arguments[0]).resolve()
    if not source.is_file() or source.suffix != '.lean':
        sys.exit(f'Lean source does not exist: {source}')
    if build:
        try:
            relative = source.relative_to(LEAN_DIR)
        except ValueError:
            sys.exit('--build is limited to this project\'s Lean sources')
        if relative.parts[0] not in ('HaagerupIzumi', 'HaagerupIzumi.lean'):
            sys.exit('--build is limited to HaagerupIzumi project modules')
        module_name = '.'.join(relative.with_suffix('').parts)
    if not guarded:
        os.execv(str(RESOURCE_GUARD), [str(RESOURCE_GUARD), '--', sys.executable,
            str(Path(__file__).resolve()), '--guarded',
            *(['--build'] if build else []), str(source), *arguments[1:]])

    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    try:
        parent_command = Path(f'/proc/{os.getppid()}/cmdline').read_bytes().split(b'\0')
    except OSError:
        sys.exit('Refusing: cannot verify the resource watchdog parent')
    if len(parent_command) < 2 or Path(os.fsdecode(parent_command[1])).resolve() != RESOURCE_GUARD.resolve():
        sys.exit('Refusing: --guarded requires the active ~/.local/bin/research-safe-run watchdog parent')
    if hard == resource.RLIM_INFINITY or hard > 6 * GIB:
        sys.exit('Refusing: the 6 GiB address-space guard is not active')
    if len(os.sched_getaffinity(0)) > 2:
        sys.exit('Refusing: CPU affinity is not limited to two CPUs')
    for argument in arguments[1:]:
        if argument.startswith(('-j', '--threads', '-s', '--tstack')):
            sys.exit('Thread count and stack size are fixed by this launcher')

    # Resolve the pinned toolchain rather than assuming the user's default.
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'],
        cwd=LEAN_DIR, text=True).strip())
    library_dir = prefix / 'lib' / 'lean'
    source_c = LEAN_DIR / 'tools' / 'lean_stack_limit.c'
    fingerprint = hashlib.sha256(source_c.read_bytes() + str(prefix).encode()).hexdigest()[:16]
    cache = LEAN_DIR / '.lake' / 'safe-runtime'
    cache.mkdir(parents=True, exist_ok=True)
    preload = cache / f'lean-stack-{fingerprint}.so'
    if not preload.exists():
        temporary = preload.with_suffix('.building.so')
        subprocess.run(['cc', '-shared', '-fPIC', str(source_c), '-o', str(temporary),
            f'-L{library_dir}', '-lleanshared', f'-Wl,-rpath,{library_dir}'], check=True)
        temporary.replace(preload)

    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '2'
    env['MIMALLOC_DISALLOW_ARENA_ALLOC'] = '1'
    env['MALLOC_ARENA_MAX'] = '2'
    prior_preload = env.get('LD_PRELOAD', '')
    env['LD_PRELOAD'] = str(preload) + (':' + prior_preload if prior_preload else '')
    lake = [str(prefix / 'bin' / 'lake'), '-d', str(LEAN_DIR)]
    if build:
        # Check the prerequisite graph without building anything. Unlike the
        # full library target, this setup operation excludes the source itself.
        # Retain real Lake trace checking; do not manufacture traces for files
        # previously elaborated manually with `-o`.
        def project_snapshot():
            paths = [LEAN_DIR / 'lakefile.toml', LEAN_DIR / 'lake-manifest.json',
                LEAN_DIR / 'lean-toolchain']
            pending = [source]
            visited = set()
            while pending:
                path = pending.pop()
                if path in visited:
                    continue
                visited.add(path)
                paths.append(path)
                imports = re.findall(r'(?m)^(?:public\s+)?(?:meta\s+)?import\s+'
                    r'(?:all\s+)?(HaagerupIzumi(?:\.[^\s]+)*)', path.read_text())
                for imported in imports:
                    pending.append(LEAN_DIR.joinpath(*imported.split('.')).with_suffix('.lean'))
            return {path: (path.stat().st_mtime_ns, path.stat().st_size) for path in paths}

        before = project_snapshot()
        result = subprocess.run([*lake, '--no-build', 'setup-file', str(source)],
            env=env, capture_output=True, text=True)
        if result.returncode:
            sys.stderr.write(result.stderr)
            sys.stderr.write(result.stdout)
            sys.exit('Refusing: build prerequisite modules first, one at a time')
        if project_snapshot() != before:
            sys.exit('Refusing: project sources changed during the prerequisite check')
        command = [*lake, '--no-cache', 'build', f'+{module_name}:leanArts']
    else:
        command = [*lake, '--no-build', 'lean', str(source), '--',
            '-j2', '-s8192', *arguments[1:]]
    os.execvpe(command[0], command, env)


if __name__ == '__main__':
    main()
