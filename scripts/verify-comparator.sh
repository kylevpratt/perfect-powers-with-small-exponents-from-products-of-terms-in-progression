#!/usr/bin/env bash
set -euo pipefail

# Run in a clean Linux checkout with the pinned toolchain installed.
# Keep the sandbox enabled. The Windows diagnostic run is not this check.
project_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$project_root"
for command_name in lake lean bwrap node; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 2; }
done
if [ "$(id -u)" -eq 0 ]; then
  echo 'Run Comparator verification as an unprivileged user.' >&2
  exit 2
fi
if [ -e .lake ]; then
  echo 'Comparator verification requires a fresh checkout without a .lake directory.' >&2
  exit 2
fi
node scripts/check-submission.mjs
lake comparator --config comparator.json --paranoid
lake build PerfectPowers.Audit Challenge Solution
lake env lean scripts/CheckChallengeInterfaces.lean
lake env lean scripts/AuditSolution.lean
