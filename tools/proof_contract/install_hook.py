#!/usr/bin/env python3
"""Install the worktree-aware V1 hook launcher without altering frozen files."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OLD = '''#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
if [ -x "$root/.githooks/pre-commit" ]; then
  exec "$root/.githooks/pre-commit" "$@"
fi
'''
WRAPPER = '''#!/usr/bin/env bash
# proof-contract-v1-launcher: preserves the immutable checker and existing checks.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
if [ -x "$root/.githooks/pre-commit" ]; then
  # The original checker computes a default repository from __file__. Give its
  # temporary copy enough parent directories; --repo still supplies the actual root.
  temporary=$(mktemp -d "${TMPDIR:-/tmp}/proof-contract-hook.XXXXXX")
  trap 'rmdir "$temporary"' EXIT
  TMPDIR="$temporary" "$root/.githooks/pre-commit" "$@"
fi
'''

def main() -> None:
    configured = subprocess.run(['git', '-C', str(ROOT), 'config', '--get', 'core.hooksPath'],
        capture_output=True, text=True)
    if configured.returncode == 0 and configured.stdout.strip():
        raise SystemExit('A custom core.hooksPath is configured; preserve and review it before installation.')
    directory = Path(subprocess.check_output(
        ['git', '-C', str(ROOT), 'rev-parse', '--git-path', 'hooks'], text=True).strip())
    if not directory.is_absolute(): directory = ROOT / directory
    hook = directory / 'pre-commit'
    if hook.exists() and hook.read_text() not in (OLD, WRAPPER):
        raise SystemExit('An unrelated pre-commit hook exists; refusing to overwrite it.')
    directory.mkdir(parents=True, exist_ok=True)
    hook.write_text(WRAPPER); hook.chmod(0o755)
    print('Installed worktree-aware V1 launcher:', hook)

if __name__ == '__main__':
    main()
