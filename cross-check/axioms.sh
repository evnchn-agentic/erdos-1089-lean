#!/usr/bin/env bash
# Fail unless every headline theorem depends on Lean's three standard axioms and nothing else.
# A green `lake build` is not enough: sorryAx can reach a theorem through an import (see README).
set -euo pipefail
cd "$(dirname "$0")/.."
F=$(mktemp -t axioms.XXXXXX).lean
trap 'rm -f "$F"' EXIT
{
  echo 'import ErdosProofs'
  for t in P1089.gDSpec_limit P1089.gDSpec_sandwich P1089.gDSpec_eq_gD P502.cardTwoDistanceSet_le; do
    echo "#print axioms ErdosProofs.$t"
  done
} > "$F"
out=$(lake env lean "$F")
echo "$out"
# 4 verdicts, and no axiom outside the standard three in any of them
[ "$(grep -cE "depends on axioms: |does not depend on any axioms" <<<"$out")" -eq 4 ] \
  && ! grep -o "axioms: \[.*\]" <<<"$out" | sed -E 's/axioms: \[//; s/\]//; s/(propext|Classical\.choice|Quot\.sound)//g' | grep -q '[^, ]' \
  || { echo "FAIL: a headline theorem is missing or uses an axiom beyond propext, Classical.choice, Quot.sound"; exit 1; }
