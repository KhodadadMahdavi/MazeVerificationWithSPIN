#!/usr/bin/env bash
set -euo pipefail

# Run this inside MSYS2 UCRT64
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

mkdir -p trails

# Some SPIN builds look for specific trail names. We ensure compatible names exist.
if [ -f pan.trail ]; then
  cp -f pan.trail promela/maze.pml.trail
  cp -f pan.trail maze.pml.trail
fi

echo "Replaying trail to trails/trail_replay.txt"
spin -t -p -g promela/maze.pml > trails/trail_replay.txt
echo "Done."
