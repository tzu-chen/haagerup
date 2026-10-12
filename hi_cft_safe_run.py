"""Compatibility entry point for the global desktop resource guard.

New commands use ~/.local/bin/research-safe-run directly, from their project
directory. This module contains no resource policy or local fallback. Old CLI
calls are replaced by the global watchdog process; historical helper imports
are delegated to the same global source.
"""

import os
from pathlib import Path
import runpy
import sys


GLOBAL_LAUNCHER = Path.home() / '.local' / 'bin' / 'research-safe-run'


def main():
    try:
        os.execv(str(GLOBAL_LAUNCHER), [str(GLOBAL_LAUNCHER), *sys.argv[1:]])
    except OSError as exc:
        sys.exit(f'Cannot execute global resource guard {GLOBAL_LAUNCHER}: {exc}')


if __name__ == '__main__':
    main()
else:
    # The expired window launcher imports these helpers. Keep a single source
    # of truth and fail closed if it is absent; never recreate a local guard.
    _guard = runpy.run_path(str(GLOBAL_LAUNCHER))
    GIB = _guard['GIB']
    LOCK = _guard['LOCK']
    LEGACY_LOCK = _guard['LEGACY_LOCK']
    open_shared_lock = _guard['open_shared_lock']
    available_bytes = _guard['available_bytes']
    cgroup_headroom = _guard['cgroup_headroom']
    group_rss = _guard['group_rss']
