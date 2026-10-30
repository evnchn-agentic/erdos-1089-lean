#!/usr/bin/env bash
# Machine-check this repository's formalisation against plby/lean-proofs'.
# Run from the repository root:  ./cross-check/run.sh
set -euo pipefail
OUT=ErdosProofs/CrossCheckScratch.lean
# Pinned like mathlib in lakefile.lean: a moving branch would let their next edit break this check.
SRC=https://raw.githubusercontent.com/plby/lean-proofs/b5abdb1b84a3ad8153daa804a9f479bf61c0125f/src/latest/ErdosProblems/Erdos1089.lean

trap 'rm -f "$OUT" /tmp/plby1089.lean' EXIT

curl -fsSL "$SRC" -o /tmp/plby1089.lean
{
  echo 'import ErdosProofs.P1089'
  echo
  # Their file from its module docstring on: their header comment and `import Mathlib.*` lines are
  # dropped because our `import Mathlib` chain already subsumes them. Nothing else is altered.
  sed -n '/^\/-!/,$p' /tmp/plby1089.lean
  sed -n '/^-- ─* CROSS-CHECK/,$p' cross-check/CrossCheck.lean
} > "$OUT"

lake env lean "$OUT"
echo
echo "cross-check OK — every theorem above type-checked."
echo "(The only expected output is their file's own trailing #print axioms.)"
