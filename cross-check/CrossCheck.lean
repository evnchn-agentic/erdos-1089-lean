/-
Cross-check of this repository's Erdős #1089 formalisation against the independent one in
`plby/lean-proofs`.

NOT SELF-CONTAINED, and deliberately so: plby/lean-proofs carries NO LICENSE file, so its
content is all-rights-reserved and is not vendored here. This file is only the second half of the
comparison — on its own it will not type-check, because the `Erdos1089` namespace it refers to is
theirs.

To run it, from the repository root:

    ./cross-check/run.sh

which fetches their source at run time, concatenates it with the `CrossCheck` namespace below, and
type-checks the pair.

What is proved here:
  * `g_eq_gDSpec`          — their `g` and our `gDSpec` are the same function
  * `their_limit_from_ours`,
    `our_limit_from_theirs` — each side's headline follows from the other's proof
  * `their_lower_bound_is_stronger` — where the two diverge, and in whose favour
-/

-- ─────────────────────── CROSS-CHECK ───────────────────────
-- Do the two independent formalisations define the SAME function?

namespace CrossCheck

open ErdosProofs.P1089

variable {d : ℕ}

/-- Their `distanceFinset`, coerced to a set, is our `DistanceSet`. -/
theorem distanceSet_eq (P : Finset (Erdos1089.Point d)) :
    DistanceSet (↑P : Set (Erdos1089.Point d)) = ↑(Erdos1089.distanceFinset P) := by
  ext r
  simp only [DistanceSet, Set.mem_setOf_eq, Finset.mem_coe,
    Erdos1089.mem_distanceFinset_iff, dist_eq_norm, Finset.mem_coe]

/-- Their distance count agrees with ours. -/
theorem distanceCount_eq (P : Finset (Erdos1089.Point d)) :
    (DistanceSet (↑P : Set (Erdos1089.Point d))).ncard = Erdos1089.distanceCount P := by
  rw [distanceSet_eq, Set.ncard_coe_finset]
  rfl

/-- The two forcing predicates agree. -/
theorem forcesDistances_iff_plby (d n m : ℕ) :
    Erdos1089.ForcesDistances d n m ↔ ErdosProofs.P1089.ForcesDistances d n m := by
  constructor
  · intro h P hPfin hPcard
    have hQ : hPfin.toFinset.card = m := by
      rw [← Set.ncard_eq_toFinset_card P hPfin]; exact hPcard
    have := h hPfin.toFinset hQ
    rwa [← distanceCount_eq, Set.Finite.coe_toFinset] at this
  · intro h P hPcard
    have := h (↑P) P.finite_toSet (by rw [Set.ncard_coe_finset]; exact hPcard)
    rwa [distanceCount_eq] at this

/-- **The two independent formalisations define the same function.** -/
theorem g_eq_gDSpec (d n : ℕ) : Erdos1089.g d n = ErdosProofs.P1089.gDSpec d n := by
  have : {m | Erdos1089.ForcesDistances d n m} = {N | ErdosProofs.P1089.ForcesDistances d n N} := by
    ext m; exact forcesDistances_iff_plby d n m
  rw [Erdos1089.g, ErdosProofs.P1089.gDSpec, this]

/-- Their headline limit, obtained from ours. -/
theorem their_limit_from_ours (n : ℕ) (hn : 2 ≤ n) :
    Filter.Tendsto (fun d : ℕ => (Erdos1089.g d n : ℝ) / (d : ℝ) ^ (n - 1))
      Filter.atTop (nhds (1 / ((n - 1).factorial : ℝ))) := by
  simpa only [g_eq_gDSpec] using ErdosProofs.P1089.gDSpec_limit n hn

/-- Our headline limit, obtained from theirs. The loop is closed: each side's
statement is derivable from the other's proof. -/
theorem our_limit_from_theirs (n : ℕ) (hn : 2 ≤ n) :
    Filter.Tendsto (fun d : ℕ => (ErdosProofs.P1089.gDSpec d n : ℝ) / (d : ℝ) ^ (n - 1))
      Filter.atTop (nhds (1 / ((n - 1).factorial : ℝ))) := by
  have h := (Erdos1089.erdos_1089 n hn).2
  simpa only [g_eq_gDSpec] using h

/-- **Divergence.** The upper bounds agree, but the lower bounds do not: theirs is
`C(d+1, n-1) + 1`, which is what erdosproblems.com states; ours is `C(d, n-1) + 1`, which is
weaker. Both give the same limit, so the headline is unaffected — but only theirs proves the
literature sandwich. Our own docstring on `MD_lower` names the missing ingredient (an affine
isometry from the sum-`s` hyperplane of `ℝ^(d+1)` down to `ℝ^d`); they built it, as
`Erdos1089.hyperplaneIsometry`. -/
theorem their_lower_bound_is_stronger (d n : ℕ) :
    Nat.choose d (n - 1) + 1 ≤ Nat.choose (d + 1) (n - 1) + 1 :=
  Nat.succ_le_succ (Nat.choose_le_choose _ (Nat.le_succ d))

end CrossCheck
