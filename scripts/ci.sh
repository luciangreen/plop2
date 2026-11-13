#!/usr/bin/env bash
# Build plop2 with plain GHC against detlog2's sources (cloned next to this repo
# or given in DETLOG2_DIR) and run the tests.
set -euo pipefail
cd "$(dirname "$0")/.."
DETLOG2_DIR=${DETLOG2_DIR:-../detlog2}
if [ ! -d "$DETLOG2_DIR/src" ]; then
  git clone --depth 1 https://github.com/luciangreen/detlog2 "$DETLOG2_DIR"
fi
ghc --version
mkdir -p build
ghc -O1 -Wall -Wno-incomplete-uni-patterns -Wno-name-shadowing -Wno-unused-do-bind \
    -isrc -i"$DETLOG2_DIR/src" -outputdir build -o build/plop2 app/Main.hs
( cd "$DETLOG2_DIR" && ./scripts/ci.sh >/dev/null 2>&1 || true )
export DETLOG2_DIR
bash tests/cli.sh
