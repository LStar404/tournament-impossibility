"""Install the reviewed linux-64 lock without solving or using other channels."""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile


def verified_download(record, cache):
    url, digest = record['url'], record['sha256']
    if not url.startswith('https://conda.anaconda.org/conda-forge/'):
        raise ValueError('Only the locked conda-forge source is permitted')
    if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise ValueError('Invalid SHA-256')
    target = cache / url.rsplit('/', 1)[1]
    if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() == digest:
        return target
    partial = target.with_suffix(target.suffix + '.part')
    subprocess.run(['curl', '--proto', '=https', '--tlsv1.2', '--fail', '--location',
                    '--show-error', '--silent', '--retry', '3', '--retry-delay', '5',
                    '--retry-max-time', '240', '--connect-timeout', '15', '--max-time', '120',
                    url, '--output', str(partial)], check=True)
    if hashlib.sha256(partial.read_bytes()).hexdigest() != digest:
        raise ValueError('SHA-256 mismatch: ' + url)
    partial.replace(target)
    return target


def main():
    lock = json.loads(Path(sys.argv[1]).read_text())
    if lock['platform'] != 'linux-64' or os.uname().machine != 'x86_64':
        raise SystemExit('This reviewed lock is only for linux-64')
    cache = Path(os.environ.get('TECTONIC_CONDA_CACHE', str(Path.home() / '.cache/paper-tectonic-conda')))
    cache.mkdir(parents=True, exist_ok=True)
    mm = verified_download(lock['micromamba'], cache)
    with tempfile.TemporaryDirectory(prefix='tectonic-installer-') as tmp:
        tmp = Path(tmp)
        with tarfile.open(mm) as archive:
            member = archive.getmember('bin/micromamba')
            if not member.isfile():
                raise ValueError('Expected a regular micromamba executable')
            binary = tmp / 'micromamba'
            binary.write_bytes(archive.extractfile(member).read())
            binary.chmod(0o755)
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
            paths = list(pool.map(lambda record: verified_download(record, cache), lock['packages']))
        explicit = tmp / 'explicit.txt'
        explicit.write_text('@EXPLICIT\n' + '\n'.join(p.resolve().as_uri() for p in paths) + '\n')
        prefix = Path(os.environ.get('TECTONIC_CONDA_PREFIX', str(Path.home() / '.local/paper-tectonic-conda')))
        # The exact local archives were all SHA-256 checked. Offline explicit mode
        # does not solve dependencies or introduce packages from another channel.
        env = dict(os.environ, CONDA_PKGS_DIRS=str(tmp / 'pkgs'), MAMBA_ROOT_PREFIX=str(tmp / 'root'))
        subprocess.run([str(binary), 'create', '--no-rc', '--offline', '-y', '-p', str(prefix),
                        '-f', str(explicit)], env=env, check=True)
        subprocess.run([str(prefix / 'bin/tectonic'), '--version'], check=True)
        if 'GITHUB_PATH' in os.environ:
            with open(os.environ['GITHUB_PATH'], 'a') as stream:
                stream.write(str(prefix / 'bin') + '\n')


if __name__ == '__main__':
    main()
