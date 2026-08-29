/-
Erdős Problem #502: largest two-distance set in ℝⁿ.

Statement (informal): the maximum size of `A ⊆ ℝⁿ` such that the set of
non-zero pairwise distances has cardinality `2` (i.e. exactly two distinct
distances) is at most `(n+2 choose 2)`.

Source: erdosproblems.com/502 + Petrov–Pohoata 2021 (arXiv:1912.08181).
The general `s`-distance bound (BBS83) is established in
`ErdosProofs/PetrovPohoata.lean`; this file packages the `s = 2` corollary.
-/

import ErdosProofs.PetrovPohoata

namespace ErdosProofs.P502

open ErdosProofs.PetrovPohoata

/-- Erdős #502: any two-distance set `P ⊆ ℝⁿ` (with both distances coming from
a fixed pair `{r₁, r₂}` of positive reals) has cardinality at most
`((n+2) choose 2)`. -/
theorem cardTwoDistanceSet_le (n : ℕ) (P : Finset (Fin n → ℝ))
    (S : Finset ℝ) (hS_card : S.card ≤ 2) (hS_pos : ∀ r ∈ S, 0 < r)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2) :
    P.card ≤ Nat.choose (n + 2) 2 :=
  cardSDistanceSet_le_finset' 2 P S hS_card hS_pos hSA

end ErdosProofs.P502
