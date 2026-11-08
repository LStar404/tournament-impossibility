"""Check Lean sources with the already-installed, read-only Lean/mathlib 4.35.0.

Usage: python check.py [lean arguments...]
"""
import subprocess
import sys

from leanlib import LEAN, ROOT, check_environment, lean_env


def main(argv):
    check_environment()
    log = ROOT / 'verification' / 'last_check.log'
    log.parent.mkdir(exist_ok=True)
    with open(log, 'w', encoding='utf-8') as handle:
        proc = subprocess.run([str(LEAN), *argv], cwd=ROOT, env=lean_env(),
                              stdout=handle, stderr=subprocess.STDOUT)
    sys.stdout.reconfigure(encoding='utf-8')
    print(log.read_text(encoding='utf-8'), end='')
    return proc.returncode


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
