"""Shared Lean invocation settings.

Child output is redirected to log files rather than captured through OS pipes,
because the sandbox used during development refused pipe creation.

Environment overrides:

* ``LEAN_BIN`` -- path to the ``lean`` executable;
* ``MATHLIB_PACKAGES`` -- directory holding the mathlib dependency checkouts.

Without them the module falls back to ``lean`` on ``PATH`` and to a local
``.lake/packages`` directory.
"""
import os
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def _lean_binary():
    explicit = os.environ.get('LEAN_BIN')
    if explicit:
        return Path(explicit)
    found = shutil.which('lean')
    if found:
        return Path(found)
    return (Path.home() / '.elan' / 'toolchains'
            / 'leanprover--lean4---v4.35.0' / 'bin' / 'lean.exe')


def _packages_dir():
    explicit = os.environ.get('MATHLIB_PACKAGES')
    if explicit:
        return Path(explicit)
    return ROOT / '.lake' / 'packages'


LEAN = _lean_binary()
PACKAGES = _packages_dir()


def check_environment():
    if not LEAN.is_file():
        raise FileNotFoundError('Lean binary not found: %s (set LEAN_BIN)' % LEAN)
    if not PACKAGES.is_dir():
        raise FileNotFoundError(
            'mathlib packages not found: %s (set MATHLIB_PACKAGES)' % PACKAGES)


def lean_env():
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(
        [str(ROOT), *sorted(str(p / '.lake/build/lib/lean')
                            for p in PACKAGES.iterdir() if p.is_dir())])
    return env
