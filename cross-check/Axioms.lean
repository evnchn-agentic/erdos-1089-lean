import ErdosProofs

/-! Fails (non-zero exit) unless every headline theorem depends only on Lean's three standard
axioms. Run from the repository root: `lake env lean cross-check/Axioms.lean`.
A green `lake build` is not enough: `sorryAx` can reach a theorem through an import (see README). -/

open Lean Elab Command in
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (· ∉ [``propext, ``Classical.choice, ``Quot.sound])
    if bad.isEmpty then logInfo m!"{n}: {axs}" else logError m!"{n} depends on {bad}"

#assert_standard_axioms ErdosProofs.P1089.gDSpec_limit ErdosProofs.P1089.gDSpec_sandwich
  ErdosProofs.P1089.gDSpec_eq_gD ErdosProofs.P502.cardTwoDistanceSet_le
