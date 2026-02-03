#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Make sure both SPIN and UCRT64 toolchain are visible even if launched from plain usr\bin\bash.exe
export PATH="$ROOT/tools/bin:/ucrt64/bin:/usr/bin:$PATH"

echo "ROOT=$ROOT"
echo "PATH=$PATH"
echo "Using spin: $(command -v spin || true)"
echo "Using gcc : $(command -v gcc || true)"

if ! command -v spin >/dev/null 2>&1; then
  echo "ERROR: spin not found on PATH."
  echo "Expected spin.exe in: $ROOT/tools/bin"
  exit 3
fi

if ! command -v gcc >/dev/null 2>&1; then
  echo "ERROR: gcc not found. Either:"
  echo "  (1) install toolchain: pacman -S --needed mingw-w64-ucrt-x86_64-gcc"
  echo "  (2) ensure MSYS2 has /ucrt64/bin available"
  exit 4
fi

mkdir -p trails

echo "[1/4] Generate verifier sources (spin -a)"
spin -a promela/maze.pml

echo "[2/4] Compile verifier (gcc -O2 -o pan pan.c)"
gcc -O2 -o pan pan.c

echo "[3/4] Run verifier (./pan -a -m200000)"
./pan -a -m200000 | tee trails/pan_output.txt

echo "[4/4] Copy trail to trails/ (if exists)"
if [ -f pan.trail ]; then
  cp -f pan.trail trails/pan.trail
  echo "Copied pan.trail -> trails/pan.trail"
fi

if [ -f maze.pml.trail ]; then
  cp -f maze.pml.trail trails/maze.pml.trail
  echo "Copied maze.pml.trail -> trails/maze.pml.trail"
fi

echo "Trail files in root:"
ls -la *.trail 2>/dev/null || true
