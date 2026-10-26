/-
Erdős Problem #1089: distinct distances of d-dimensional point sets.

Statement (informal). Let `g_d(n)` be the minimum cardinality such that every
set of `g_d(n)` points in `ℝ^d` determines at least `n` distinct (non-zero)
distances. Then for `n ≥ 2`,
    `lim_{d → ∞} g_d(n) / d^{n-1} = 1 / (n-1)!`.

Sources:
* The Aletheia writeup, arXiv:2601.22401 §4.4 (the source artifact this file
  transcribes; see the README for provenance).
* The cited literature sandwich:
    `(d+1 choose n-1) + 1  ≤  g_d(n)  ≤  (d+n-1 choose n-1) + 1`,
  lower bound by Aletheia, upper bound by Bannai–Bannai–Stanton 1983.

This file follows the artifact's structure:
  1.  Definitions of `DistanceSet`, `IsSDistanceSet`, `MD`, `gD`.
  2.  `gD = MD + 1` and the trivial `n = 1` case.
  3.  Lower bound (Aletheia construction)            — proved here.
  4.  Upper bound (BBS83)                            — proved via `ErdosProofs.PetrovPohoata`.
  5.  Limit via the squeeze theorem                  — proved here.

The Bannai–Bannai–Stanton 1983 bound `M_d(s) ≤ (d+s choose s)` is *not* available
in mathlib (it requires the polynomial method on indicator polynomials of point
sets, dimension `= (d+s choose s)`). It was originally a `MATHLIB-MISSING` sorry;
it is now discharged through the Petrov–Pohoata 2021 formalisation in
`ErdosProofs/PetrovPohoata.lean`, so nothing in this file is conditional any more.
As of 2026-08-28 both files are sorry-free and `#print axioms gD_limit` reports
only `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib
import ErdosProofs.PetrovPohoata

namespace ErdosProofs.P1089

open scoped BigOperators
open Filter Topology Asymptotics

/-! ## 1. Basic definitions -/

/-- The set of (non-zero) pairwise distances of a set of points in `ℝ^d`. -/
def DistanceSet {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {r | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ‖x - y‖ = r}

/-- `P` is an `s`-distance set: finite, with at most `s` distinct pairwise
distances. -/
def IsSDistanceSet (d s : ℕ) (P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  P.Finite ∧ (DistanceSet P).ncard ≤ s

/-- The distance set of a finite point set is finite. -/
theorem DistanceSet_finite {d : ℕ} {P : Set (EuclideanSpace ℝ (Fin d))} (hP : P.Finite) :
    (DistanceSet P).Finite := by
  have h := (hP.prod hP).image (fun p : _ × _ => ‖p.1 - p.2‖)
  refine h.subset ?_
  rintro r ⟨a, ha, b, hb, _, rfl⟩
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Distance sets are monotone under inclusion: shrinking a point set can only remove
distances, never add them. -/
theorem DistanceSet_mono {d : ℕ} {P Q : Set (EuclideanSpace ℝ (Fin d))} (h : Q ⊆ P) :
    DistanceSet Q ⊆ DistanceSet P := by
  rintro r ⟨a, ha, b, hb, hab, rfl⟩
  exact ⟨a, h ha, b, h hb, hab, rfl⟩

/-- `MD d s` is the supremum of cardinalities of `s`-distance sets in `ℝ^d`.
For `s ≥ 1` this is bounded above by `(d+s choose s)` (Bannai–Bannai–Stanton);
for `s = 0` only one-point sets qualify, so `MD d 0 = 1`. -/
noncomputable def MD (d s : ℕ) : ℕ :=
  sSup {k | ∃ P : Set (EuclideanSpace ℝ (Fin d)), IsSDistanceSet d s P ∧ P.ncard = k}

/-- `gD d n` is the minimum cardinality forcing at least `n` distinct distances.
By definition, `gD d n = MD d (n-1) + 1`. -/
noncomputable def gD (d n : ℕ) : ℕ := MD d (n - 1) + 1

/-! ## 2. Tiny identities -/

theorem gD_eq_MD_add_one (d n : ℕ) : gD d n = MD d (n - 1) + 1 := rfl

theorem gD_one (d : ℕ) : gD d 1 = 2 := by
  show MD d 0 + 1 = 2
  -- Key lemma: any 0-distance set has cardinality ≤ 1.
  -- (No distinct pair = no nonzero distance; finiteness handles the casts.)
  have step : ∀ P : Set (EuclideanSpace ℝ (Fin d)),
      IsSDistanceSet d 0 P → P.ncard ≤ 1 := by
    rintro P ⟨hPfin, hPdist⟩
    by_contra hPgt
    have hPgt : 1 < P.ncard := Nat.lt_of_not_ge hPgt
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard hPfin).mp hPgt
    have hmem : ‖x - y‖ ∈ DistanceSet P := ⟨x, hx, y, hy, hxy, rfl⟩
    have hDPfin : (DistanceSet P).Finite := DistanceSet_finite hPfin
    have : 0 < (DistanceSet P).ncard := (Set.ncard_pos hDPfin).mpr ⟨_, hmem⟩
    omega
  -- The empty set witnesses 0 ∈ {attainable cardinalities}; {0} witnesses 1.
  have witnessSet : {k | ∃ P : Set (EuclideanSpace ℝ (Fin d)),
      IsSDistanceSet d 0 P ∧ P.ncard = k}.Nonempty :=
    ⟨0, ∅, ⟨Set.finite_empty, by simp [DistanceSet]⟩, by simp⟩
  have hbdd : BddAbove {k | ∃ P : Set (EuclideanSpace ℝ (Fin d)),
      IsSDistanceSet d 0 P ∧ P.ncard = k} :=
    ⟨1, fun _ ⟨P, hP, hk⟩ => hk ▸ step P hP⟩
  have hMD : MD d 0 = 1 := by
    apply le_antisymm
    · apply csSup_le witnessSet
      rintro _ ⟨P, hP, rfl⟩
      exact step P hP
    · apply le_csSup hbdd
      refine ⟨{(0 : EuclideanSpace ℝ (Fin d))},
        ⟨Set.finite_singleton _, ?_⟩, Set.ncard_singleton _⟩
      simp [DistanceSet]
  rw [hMD]

/-! ## 3. Lower bound (Aletheia construction)

Take the binary vectors of length `d+1` with exactly `s` ones, mapped into
`ℝ^{d+1}`. Cardinality: `(d+1 choose s)`. The squared pairwise distances form
a subset of `{2(s-k) | 0 ≤ k ≤ s-1}`, so at most `s` distinct values.
This gives an `s`-distance set in `ℝ^{d+1}`, embeddable into `ℝ^d` via the
hyperplane `Σ xᵢ = s` (which is affine-isometric to `ℝ^d`). -/

/-- Lift a function `Fin (d+1) → ℝ` to a point of `EuclideanSpace ℝ (Fin (d+1))`.
The carrier types are equal but not syntactically; mathlib uses `WithLp.equiv`. -/
noncomputable def toEucl {d : ℕ} (v : Fin (d + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  (WithLp.equiv 2 _).symm v

/-- The indicator-of-subset map. Sends an `s`-element subset of `Fin (d+1)`
to its 0/1 vector in `ℝ^{d+1}`. -/
noncomputable def indicatorVec {d : ℕ} (S : Finset (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  toEucl (fun i => if i ∈ S then (1 : ℝ) else 0)

/-- The Aletheia construction: indicator vectors of `s`-element subsets of
`Fin (d+1)`, as points in `EuclideanSpace ℝ (Fin (d+1))`. -/
noncomputable def AletheiaSet (d s : ℕ) : Finset (EuclideanSpace ℝ (Fin (d + 1))) :=
  ((Finset.univ : Finset (Fin (d + 1))).powersetCard s).image indicatorVec

theorem indicatorVec_injective (d : ℕ) :
    Function.Injective (indicatorVec : Finset (Fin (d + 1)) → _) := by
  intro S T h
  -- h : indicatorVec S = indicatorVec T (in EuclideanSpace ℝ (Fin (d+1)))
  -- The carrier map is `(WithLp.equiv 2 _).symm ∘ (fun S i => ite (i ∈ S) 1 0)`.
  -- Apply Equiv injectivity to peel `.symm`, then go pointwise.
  have h' : (fun j => if j ∈ S then (1 : ℝ) else 0) =
            (fun j => if j ∈ T then (1 : ℝ) else 0) :=
    (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm.injective h
  ext i
  have hi := congr_fun h' i
  -- hi : (if i ∈ S then 1 else 0) = (if i ∈ T then 1 else 0) in ℝ
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

theorem AletheiaSet_card (d s : ℕ) :
    (AletheiaSet d s).card = Nat.choose (d + 1) s := by
  unfold AletheiaSet
  rw [Finset.card_image_of_injective _ (indicatorVec_injective d),
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The squared norm of the difference of two indicator vectors of `s`-subsets
`S, T` (of a common ground set) is `2 * (s - |S ∩ T|)`. Pure combinatorial
identity: `(u i - v i)² = u i + v i - 2 * u i * v i` pointwise for `0/1`-valued
`u, v`, and `∑ u = |S|`, `∑ v = |T|`, `∑ u*v = |S ∩ T|`. -/
theorem indicatorVec_dist_sq {d : ℕ} (S T : Finset (Fin (d + 1))) :
    ‖indicatorVec S - indicatorVec T‖ ^ 2 =
      (S.card : ℝ) + T.card - 2 * (S ∩ T).card := by
  have hnorm := EuclideanSpace.real_norm_sq_eq
    (indicatorVec S - indicatorVec T : EuclideanSpace ℝ (Fin (d + 1)))
  rw [hnorm]
  have hpt : ∀ i : Fin (d + 1),
      ((indicatorVec S - indicatorVec T) i) ^ 2 =
        (if i ∈ S then (1 : ℝ) else 0) + (if i ∈ T then (1 : ℝ) else 0)
          - 2 * (if i ∈ S ∩ T then (1 : ℝ) else 0) := by
    intro i
    show ((indicatorVec S : EuclideanSpace ℝ (Fin (d+1))) i
            - (indicatorVec T : EuclideanSpace ℝ (Fin (d+1))) i) ^ 2 = _
    show ((toEucl (fun j => if j ∈ S then (1:ℝ) else 0) : EuclideanSpace ℝ (Fin (d+1))) i
            - (toEucl (fun j => if j ∈ T then (1:ℝ) else 0) : EuclideanSpace ℝ (Fin (d+1))) i) ^ 2
          = _
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [toEucl, hS, hT, Finset.mem_inter]; norm_num
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      ← Finset.mul_sum, Finset.sum_boole]
  have hSuniv : (Finset.univ : Finset (Fin (d+1))).filter (· ∈ S) = S := by
    ext i; simp
  have hTuniv : (Finset.univ : Finset (Fin (d+1))).filter (· ∈ T) = T := by
    ext i; simp
  have hSTuniv : (Finset.univ : Finset (Fin (d+1))).filter (· ∈ S ∩ T) = S ∩ T := by
    ext i; simp
  rw [hSuniv, hTuniv, hSTuniv]

theorem AletheiaSet_isSDistanceSet (d s : ℕ) (_hs : 1 ≤ s) :
    IsSDistanceSet (d + 1) s ((AletheiaSet d s : Finset _) : Set _) := by
  refine ⟨(AletheiaSet d s).finite_toSet, ?_⟩
  classical
  -- Every realised distance is `√(2 * (s - k))` for some `k < s`
  -- (`k` = the intersection size of the two witnessing `s`-subsets).
  have hsub : DistanceSet
      ((AletheiaSet d s : Finset (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆
      (fun k : ℕ => Real.sqrt (2 * ((s : ℝ) - k))) '' ((Finset.range s : Finset ℕ) : Set ℕ) := by
    rintro r ⟨x, hx, y, hy, hxy, rfl⟩
    rw [Finset.mem_coe] at hx hy
    unfold AletheiaSet at hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨S, hS, rfl⟩ := hx
    obtain ⟨T, hT, rfl⟩ := hy
    rw [Finset.mem_powersetCard] at hS hT
    obtain ⟨-, hScard⟩ := hS
    obtain ⟨-, hTcard⟩ := hT
    have hST : S ≠ T := fun h => hxy (h ▸ rfl)
    -- `S ∩ T` is a *proper* subset of `S` (else `S ⊆ T`, and equal cards force `S = T`).
    have hnsub : ¬ S ⊆ T := fun hsub =>
      hST (Finset.eq_of_subset_of_card_le hsub (by rw [hScard, hTcard]))
    have hproper : S ∩ T ⊂ S :=
      ssubset_of_ne_of_subset
        (fun heq => hnsub (heq ▸ Finset.inter_subset_right)) Finset.inter_subset_left
    have hk_lt : (S ∩ T).card < s := hScard ▸ Finset.card_lt_card hproper
    refine ⟨(S ∩ T).card, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]; exact hk_lt
    · show Real.sqrt (2 * ((s : ℝ) - (S ∩ T).card)) = ‖indicatorVec S - indicatorVec T‖
      have hnn : (0:ℝ) ≤ ‖indicatorVec S - indicatorVec T‖ := norm_nonneg _
      have heq : (2 * ((s:ℝ) - (S ∩ T).card)) = ‖indicatorVec S - indicatorVec T‖ ^ 2 := by
        rw [indicatorVec_dist_sq S T, hScard, hTcard]; ring
      rw [heq, Real.sqrt_sq hnn]
  calc (DistanceSet
        ((AletheiaSet d s : Finset (EuclideanSpace ℝ (Fin (d + 1)))) :
          Set (EuclideanSpace ℝ (Fin (d + 1))))).ncard
      ≤ ((fun k : ℕ => Real.sqrt (2 * ((s : ℝ) - k))) ''
          ((Finset.range s : Finset ℕ) : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub
          (Set.Finite.image _ (Finset.range s).finite_toSet)
    _ ≤ ((Finset.range s : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_image_le (Finset.range s).finite_toSet
    _ = s := by rw [Set.ncard_coe_finset, Finset.card_range]

/-! ## 4. Upper bound — Bannai–Bannai–Stanton 1983

This is the deep input. The proof uses the polynomial method: indicator
polynomials of the points span a subspace of dimension `≤ (d+s choose s)`. Not
in mathlib, won't be added here. We state the **pointwise** form and derive
both the supremum-form `MD_upper` and the `BddAbove` premise needed for
`MD_lower_dim_plus_one` from it. -/

/-- Bannai–Bannai–Stanton 1983 (pointwise). Any `s`-distance set in `ℝ^d` has
at most `(d+s choose s)` elements. Routed via the Petrov–Pohoata 2021 simple
proof in `ErdosProofs/PetrovPohoata.lean` (sorry-free as of 2026-08-28). -/
theorem cardSDistanceSet_le (d s : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d))) (hP : IsSDistanceSet d s P) :
    P.ncard ≤ Nat.choose (d + s) s := by
  obtain ⟨hPfin, hPdist_card⟩ := hP
  -- Convert to PP21's `Fin d → ℝ` Finset form via WithLp.equiv.
  classical
  let toFn : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 _
  let P_finset : Finset (Fin d → ℝ) := hPfin.toFinset.image toFn
  -- DistanceSet of P is finite (subset of finite × finite under norm).
  have hDPfin : (DistanceSet P).Finite := DistanceSet_finite hPfin
  let S : Finset ℝ := hDPfin.toFinset
  -- P.ncard = P_finset.card via injectivity of WithLp.equiv 2
  have hP_card : P_finset.card = P.ncard := by
    show (hPfin.toFinset.image toFn).card = P.ncard
    rw [Finset.card_image_of_injective _ (WithLp.equiv 2 _).injective,
        ← Set.ncard_eq_toFinset_card _ hPfin]
  -- DistanceSet.ncard ≤ s ⇒ S.card ≤ s
  have hS_card : S.card ≤ s := by
    show hDPfin.toFinset.card ≤ s
    rw [← Set.ncard_eq_toFinset_card _ hDPfin]
    exact hPdist_card
  have hS_pos : ∀ r ∈ S, 0 < r := by
    intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨x, _, y, _, hxy, rfl⟩ := hr
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hxy
  have hSA : ∀ a ∈ P_finset, ∀ b ∈ P_finset, a ≠ b →
      ∃ r ∈ S, ∑ i, (a i - b i) ^ 2 = r ^ 2 := by
    intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [Set.Finite.mem_toFinset] at hx hy
    have hxy : x ≠ y := fun h => hab (h ▸ rfl)
    refine ⟨‖x - y‖, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact ⟨x, hx, y, hy, hxy, rfl⟩
    · -- ∑ i, ((toFn x) i - (toFn y) i)^2 = ‖x - y‖^2
      have h := EuclideanSpace.real_norm_sq_eq (x - y)
      simp only [toFn]
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      rfl
  have h := PetrovPohoata.cardSDistanceSet_le_finset'
    s P_finset S hS_card hS_pos hSA
  rw [hP_card] at h
  exact h

/-- The set of cardinalities of `s`-distance sets is bounded above by
`(d + s choose s)`, courtesy of `cardSDistanceSet_le`. -/
private theorem MD_set_bddAbove (d s : ℕ) :
    BddAbove {k | ∃ P : Set (EuclideanSpace ℝ (Fin d)),
      IsSDistanceSet d s P ∧ P.ncard = k} :=
  ⟨Nat.choose (d + s) s, by
    rintro _ ⟨P, hP, rfl⟩
    exact cardSDistanceSet_le d s P hP⟩

/-- The set of cardinalities of `s`-distance sets contains `0` (the empty set),
hence is non-empty. -/
private theorem MD_set_nonempty (d s : ℕ) :
    {k | ∃ P : Set (EuclideanSpace ℝ (Fin d)),
      IsSDistanceSet d s P ∧ P.ncard = k}.Nonempty :=
  ⟨0, ∅, ⟨Set.finite_empty, by simp [DistanceSet]⟩, by simp⟩

/-- Bannai–Bannai–Stanton 1983 (supremum form). Derived from the pointwise
version via `csSup_le`. -/
theorem MD_upper (d s : ℕ) : MD d s ≤ Nat.choose (d + s) s := by
  apply csSup_le (MD_set_nonempty d s)
  rintro _ ⟨P, hP, rfl⟩
  exact cardSDistanceSet_le d s P hP

/-! ### Fidelity: `gD` really is the quantity Erdős asks about

`gD` is *defined* as `MD d (n-1) + 1`, which is the problem read from the maximising end.
Erdős's own wording is the minimising end — the least `N` such that *every* `N`-point set
already determines `n` distinct distances. The two are equivalent, and this section proves
it rather than asserting it in a comment, so that the headline theorem is about the quantity
the problem actually names.

Worth noting where the equivalence gets its strength: **both** directions go through
`MD_set_bddAbove`, i.e. through Bannai–Bannai–Stanton. Without a bound, `sSup` on `ℕ` returns
its junk value `0` and `MD` means nothing. The bridge that looks like bookkeeping rests on the
same theorem the headline does. -/

/-- `ForcesDistances d n N`: every `N`-point set in `ℝ^d` determines at least `n` distinct
distances. This is Erdős's wording, transcribed literally.

⚠️ Degenerate at `d = 0`: `EuclideanSpace ℝ (Fin 0)` is a single point, so no set of size `≥ 2`
exists and `ForcesDistances 0 n N` holds *vacuously* for every `N ≥ 2`, giving `gDSpec 0 n = 2`.
`gD 0 n` is also `2`, so `gDSpec_eq_gD` is true there — but true because both sides collapse, not
because anything was verified. The problem is about `d → ∞`; `gD_limit` requires no lower bound on
`d`, and nothing downstream reads `d = 0`. Recorded rather than excluded so the convention is
explicit. -/
def ForcesDistances (d n N : ℕ) : Prop :=
  ∀ P : Set (EuclideanSpace ℝ (Fin d)), P.Finite → P.ncard = N → n ≤ (DistanceSet P).ncard

/-- `gDSpec d n` is `g_d(n)` exactly as the problem states it: the least `N` that forces `n`
distinct distances. -/
noncomputable def gDSpec (d n : ℕ) : ℕ := sInf {N | ForcesDistances d n N}

/-- The bridge. `N` forces `n` distances iff `N` is beyond the reach of every
`(n-1)`-distance set.

Forward: if some `(n-1)`-distance set were as large as `N`, shrink it to exactly `N` points
(`DistanceSet_mono` keeps the distance count down) and it witnesses a failure to force.
Backward: an `N`-point set with fewer than `n` distances *is* an `(n-1)`-distance set, so `N`
cannot exceed `MD d (n-1)`. -/
theorem forcesDistances_iff (d n N : ℕ) (hn : 1 ≤ n) :
    ForcesDistances d n N ↔ MD d (n - 1) < N := by
  constructor
  · intro hF
    by_contra hle
    push Not at hle
    obtain ⟨P0, hP0, hP0card⟩ :=
      Nat.sSup_mem (MD_set_nonempty d (n - 1)) (MD_set_bddAbove d (n - 1))
    have hle' : N ≤ P0.ncard := by rw [hP0card]; exact hle
    obtain ⟨Q, hQsub, hQcard⟩ := Set.exists_subset_card_eq hle'
    have hQfin : Q.Finite := hP0.1.subset hQsub
    have hn_le := hF Q hQfin hQcard
    have hmono : (DistanceSet Q).ncard ≤ (DistanceSet P0).ncard :=
      Set.ncard_le_ncard (DistanceSet_mono hQsub) (DistanceSet_finite hP0.1)
    have := hP0.2
    omega
  · intro hlt P hPfin hPcard
    by_contra hn_gt
    push Not at hn_gt
    have hP : IsSDistanceSet d (n - 1) P := ⟨hPfin, by omega⟩
    have : N ≤ MD d (n - 1) := by
      rw [← hPcard]
      exact le_csSup (MD_set_bddAbove d (n - 1)) ⟨P, hP, rfl⟩
    omega

/-- **The fidelity theorem.** For `n ≥ 1`, the literal reading of the problem and the definition
this file works with agree.

The hypothesis is not decorative: at `n = 0`, `ForcesDistances d 0 N` holds for every `N`, so
`gDSpec d 0 = 0`, while `gD d 0 = MD d 0 + 1 = 2`. Dropping `hn` breaks the forward direction of
`forcesDistances_iff` at its `omega`. -/
theorem gDSpec_eq_gD (d n : ℕ) (hn : 1 ≤ n) : gDSpec d n = gD d n := by
  have hset : {N | ForcesDistances d n N} = {N | MD d (n - 1) < N} := by
    ext N; exact forcesDistances_iff d n N hn
  have hne : {N | MD d (n - 1) < N}.Nonempty := ⟨MD d (n - 1) + 1, by simp⟩
  rw [gDSpec, hset, gD_eq_MD_add_one]
  refine le_antisymm (Nat.sInf_le (by simp)) ?_
  have := Nat.sInf_mem hne
  simp only [Set.mem_setOf_eq] at this
  omega

/-- Non-vacuity: `ForcesDistances` is not trivially true. A one-point set determines no
distance, so one point does not force one. Proved straight from the definition, without
routing through `MD`. -/
theorem not_forcesDistances_one (d : ℕ) : ¬ ForcesDistances d 1 1 := by
  intro h
  have hP : ({0} : Set (EuclideanSpace ℝ (Fin d))).ncard = 1 := Set.ncard_singleton _
  have hcard := h {0} (Set.finite_singleton _) hP
  have hempty : DistanceSet ({0} : Set (EuclideanSpace ℝ (Fin d))) = ∅ := by
    ext r
    simp only [DistanceSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨a, rfl, b, rfl, hab, rfl⟩
    exact hab rfl
  rw [hempty] at hcard
  simp at hcard

/-- Cross-check: the literal definition reproduces the independently-proved `gD d 1 = 2`. -/
example (d : ℕ) : gDSpec d 1 = 2 := by
  rw [gDSpec_eq_gD d 1 le_rfl]; exact gD_one d

/-- Lower bound on `MD` over `ℝ^{d+1}`: the Aletheia construction realises an
`s`-distance set of size `(d+1 choose s)`. -/
theorem MD_lower_dim_plus_one (d s : ℕ) (hs : 1 ≤ s) :
    Nat.choose (d + 1) s ≤ MD (d + 1) s := by
  apply le_csSup (MD_set_bddAbove (d + 1) s)
  refine ⟨((AletheiaSet d s : Finset _) : Set _),
    AletheiaSet_isSDistanceSet d s hs, ?_⟩
  rw [Set.ncard_coe_finset]
  exact AletheiaSet_card d s

/-- A map that preserves distances on `P` carries `P`'s distance set over unchanged. -/
theorem DistanceSet_image {d d' : ℕ} {P : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d')}
    (hf : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y‖ = ‖x - y‖) :
    DistanceSet (f '' P) = DistanceSet P := by
  ext r
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy, rfl⟩
    exact ⟨x, hx, y, hy, fun h => hxy (h ▸ rfl), (hf x hx y hy).symm⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, fun h => hxy ?_, hf x hx y hy⟩
    rw [← sub_eq_zero, ← norm_eq_zero, ← hf x hx y hy, h, sub_self, norm_zero]

/-- An `s`-distance set that embeds distance-preservingly into `ℝ^d'` bounds `MD d' s`. -/
theorem le_MD_of_isometry {d d' s : ℕ} {P : Set (EuclideanSpace ℝ (Fin d))}
    (hP : IsSDistanceSet d s P)
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d')}
    (hf : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y‖ = ‖x - y‖) :
    P.ncard ≤ MD d' s := by
  have hinj : Set.InjOn f P := fun x hx y hy h => by
    rw [← sub_eq_zero, ← norm_eq_zero, ← hf x hx y hy, h, sub_self, norm_zero]
  apply le_csSup (MD_set_bddAbove d' s)
  refine ⟨f '' P, ⟨hP.1.image f, ?_⟩, hinj.ncard_image⟩
  rw [DistanceSet_image hf]
  exact hP.2

/-- The all-ones vector, normal to the hyperplanes `Σ xᵢ = c`. -/
noncomputable def onesVec (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) := toEucl fun _ => 1

/-- The direction of the hyperplanes `Σ xᵢ = c` is `d`-dimensional. -/
theorem finrank_onesVec_orthogonal (d : ℕ) :
    Module.finrank ℝ (ℝ ∙ onesVec d)ᗮ = d := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ onesVec d)
  rw [finrank_span_singleton] at h
  · simp at h; omega
  · intro h0
    have := congrFun (congrArg (WithLp.equiv 2 _) h0) 0
    simp [onesVec, toEucl] at this

/-- Two points with equal coordinate sums differ by a vector orthogonal to `onesVec`. -/
theorem sub_mem_onesVec_orthogonal {d : ℕ} {x y : EuclideanSpace ℝ (Fin (d + 1))}
    (h : ∑ i, x i = ∑ i, y i) : x - y ∈ (ℝ ∙ onesVec d)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [onesVec, toEucl, PiLp.inner_apply, WithLp.equiv_symm_apply, PiLp.sub_apply,
    real_inner_eq_re_inner, RCLike.re_to_real]
  simp [Finset.sum_sub_distrib, h]

/-- Project `ℝ^{d+1}` onto the hyperplane direction and identify it with `ℝ^d`. Restricted to
any hyperplane `Σ xᵢ = c` this is an isometry. -/
noncomputable def hyperplaneToEucl (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d) := fun x =>
  ((stdOrthonormalBasis ℝ (ℝ ∙ onesVec d)ᗮ).reindex
      (finCongr (finrank_onesVec_orthogonal d))).repr
    ((ℝ ∙ onesVec d)ᗮ.orthogonalProjection x)

theorem hyperplaneToEucl_dist {d : ℕ} {x y : EuclideanSpace ℝ (Fin (d + 1))}
    (h : ∑ i, x i = ∑ i, y i) :
    ‖hyperplaneToEucl d x - hyperplaneToEucl d y‖ = ‖x - y‖ := by
  unfold hyperplaneToEucl
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, ← map_sub,
    ← Submodule.coe_mk (x - y) (sub_mem_onesVec_orthogonal h),
    Submodule.orthogonalProjection_mem_subspace_eq_self, Submodule.coe_norm]

theorem indicatorVec_sum {d : ℕ} (S : Finset (Fin (d + 1))) :
    ∑ i, indicatorVec S i = S.card := by
  simp [indicatorVec, toEucl]

/-- **Lower bound on `MD`, the artifact's full strength.** The Aletheia set lies in the
hyperplane `Σ xᵢ = s` of `ℝ^{d+1}`, which `hyperplaneToEucl` maps isometrically into `ℝ^d`. -/
theorem MD_lower (d s : ℕ) (hs : 1 ≤ s) :
    Nat.choose (d + 1) s ≤ MD d s := by
  classical
  have hsum : ∀ x ∈ ((AletheiaSet d s : Finset _) : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∑ i, x i = s := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    rw [indicatorVec_sum, (Finset.mem_powersetCard.mp hS).2]
  have h := le_MD_of_isometry (d' := d) (AletheiaSet_isSDistanceSet d s hs)
    (f := hyperplaneToEucl d) fun x hx y hy =>
      hyperplaneToEucl_dist ((hsum x hx).trans (hsum y hy).symm)
  rwa [Set.ncard_coe_finset, AletheiaSet_card] at h

/-! ## 5. Sandwich for `gD` and the limit -/

theorem gD_sandwich (d n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ gD d n
      ∧ gD d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 := by
  have hge : 1 ≤ n - 1 := by omega
  have hadd : d + (n - 1) = d + n - 1 := by omega
  refine ⟨?_, ?_⟩
  · -- lower
    have hlo := MD_lower d (n - 1) hge
    rw [gD_eq_MD_add_one]
    omega
  · -- upper
    have hub := MD_upper d (n - 1)
    rw [gD_eq_MD_add_one, ← hadd]
    omega

/-- The literature sandwich `C(d+1, n-1) + 1 ≤ g_d(n) ≤ C(d+n-1, n-1) + 1`, stated over the
literal reading `gDSpec`. -/
theorem gDSpec_sandwich (d n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ gDSpec d n
      ∧ gDSpec d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 := by
  rw [gDSpec_eq_gD d n (by omega)]
  exact gD_sandwich d n hn

/-! ### Auxiliary: asymptotics of `Nat.choose (d+c) k`

The key elementary fact: `binom(d+c, k) / d^k → 1/k!` as `d → ∞`.

Mathematically, `binom(d+c, k) = (d+c)·(d+c-1)·…·(d+c-k+1)/k!`, and the
leading term of the numerator is `d^k`, so the ratio with `d^k` tends to
`1/k!`.

Proved by an elementary squeeze rather than via `Asymptotics.isEquivalent_choose`:
the `IsEquivalent` route needs the shift `n = d + c` and `(d+c)^k ~ d^k` stitched
together, and the resulting function-composition forms (`Pi.div` vs explicit
lambdas) resist `simpa` / `tendsto_congr'`. Going through `Nat.descFactorial`
instead gives the two integer bounds

`(d+c+1-k)^k ≤ k! * binom(d+c,k) ≤ (d+c)^k`

directly, and both envelopes `((d + a)/d)^k / k!` tend to `1/k!` for any real
shift `a`. -/

private theorem choose_shift_div_pow_tendsto (k c : ℕ) :
    Tendsto (fun d : ℕ => ((Nat.choose (d + c) k : ℕ) : ℝ) / (d : ℝ) ^ k)
      atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  -- `(d + a) / d → 1` for any real shift `a`.
  have hshift : ∀ a : ℝ, Tendsto (fun d : ℕ => ((d : ℝ) + a) / (d : ℝ)) atTop (𝓝 1) := by
    intro a
    have h0 : Tendsto (fun d : ℕ => a / (d : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat a
    have h1 : Tendsto (fun d : ℕ => 1 + a / (d : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h0
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp
  -- Both squeeze envelopes have the shape `((d + a) / d) ^ k / k!`.
  have henv : ∀ a : ℝ,
      Tendsto (fun d : ℕ => (((d : ℝ) + a) / (d : ℝ)) ^ k / (k.factorial : ℝ))
        atTop (𝓝 (1 / (k.factorial : ℝ))) := by
    intro a
    simpa using ((hshift a).pow k).div_const (k.factorial : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (henv ((c : ℝ) + 1 - (k : ℝ))) (henv (c : ℝ)) ?_ ?_
  · -- lower envelope: `(d+c+1-k)^k ≤ (d+c).descFactorial k = k! * binom(d+c,k)`
    filter_upwards [eventually_ge_atTop (max 1 k)] with d hd
    have hd1 : 1 ≤ d := le_trans (le_max_left _ _) hd
    have hdk : k ≤ d := le_trans (le_max_right _ _) hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hcast : ((d : ℝ) + ((c : ℝ) + 1 - (k : ℝ))) = ((d + c + 1 - k : ℕ) : ℝ) := by
      have hle : k ≤ d + c + 1 := by omega
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have hstep : ((d + c + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ)
        ≤ (Nat.choose (d + c) k : ℝ) := by
      rw [div_le_iff₀ hfac]
      have hn : (d + c + 1 - k) ^ k ≤ Nat.choose (d + c) k * k.factorial := by
        calc (d + c + 1 - k) ^ k
            ≤ (d + c).descFactorial k := Nat.pow_sub_le_descFactorial (d + c) k
          _ = k.factorial * Nat.choose (d + c) k :=
              Nat.descFactorial_eq_factorial_mul_choose _ _
          _ = Nat.choose (d + c) k * k.factorial := Nat.mul_comm _ _
      exact_mod_cast hn
    calc (((d : ℝ) + ((c : ℝ) + 1 - (k : ℝ))) / (d : ℝ)) ^ k / (k.factorial : ℝ)
        = ((d + c + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) / (d : ℝ) ^ k := by
          rw [hcast, div_pow]; ring
      _ ≤ (Nat.choose (d + c) k : ℝ) / (d : ℝ) ^ k := by gcongr
  · -- upper envelope: `k! * binom(d+c,k) = (d+c).descFactorial k ≤ (d+c)^k`
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hcast : ((d : ℝ) + (c : ℝ)) = ((d + c : ℕ) : ℝ) := by push_cast; ring
    have hstep : (Nat.choose (d + c) k : ℝ) ≤ ((d + c : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := by
      rw [le_div_iff₀ hfac]
      have hn : Nat.choose (d + c) k * k.factorial ≤ (d + c) ^ k := by
        calc Nat.choose (d + c) k * k.factorial
            = k.factorial * Nat.choose (d + c) k := Nat.mul_comm _ _
          _ = (d + c).descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
          _ ≤ (d + c) ^ k := Nat.descFactorial_le_pow _ _
      exact_mod_cast hn
    calc (Nat.choose (d + c) k : ℝ) / (d : ℝ) ^ k
        ≤ ((d + c : ℕ) : ℝ) ^ k / (k.factorial : ℝ) / (d : ℝ) ^ k := by gcongr
      _ = (((d : ℝ) + (c : ℝ)) / (d : ℝ)) ^ k / (k.factorial : ℝ) := by
          rw [hcast, div_pow]; ring

/-- **Theorem 5 (n ≥ 2).**
For each `n ≥ 2`, `g_d(n) / d^{n-1} → 1 / (n-1)!` as `d → ∞`. -/
theorem gD_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (gD d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) := by
  -- Lower envelope: ((Nat.choose(d+1)(n-1) + 1) : ℝ) / d^(n-1)
  -- Upper envelope: ((Nat.choose(d+n-1)(n-1) + 1) : ℝ) / d^(n-1)
  -- Both → 1/(n-1)!.
  have hlow_lim :
      Tendsto (fun d : ℕ => (((Nat.choose d (n - 1) + 1 : ℕ)) : ℝ) / (d : ℝ) ^ (n - 1))
        atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) := by
    have h := choose_shift_div_pow_tendsto (n - 1) 0
    -- (Nat.choose d (n-1) + 1) / d^(n-1) = Nat.choose d (n-1) / d^(n-1) + 1/d^(n-1)
    -- The "+1" term vanishes as d → ∞.
    have hsmall : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ (n - 1)) atTop (𝓝 0) := by
      have hpos : 0 < n - 1 := by omega
      have h1 : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun d : ℕ => ((1 : ℝ) / (d : ℝ)) ^ (n - 1)) atTop (𝓝 0) := by
        have := h1.pow (n - 1)
        rwa [zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at this
      refine h2.congr fun d => ?_
      rw [div_pow, one_pow]
    have := h.add hsmall
    have rewrite : (fun d : ℕ => ((Nat.choose (d + 0) (n - 1) : ℕ) : ℝ) / (d : ℝ) ^ (n - 1)
          + (1 : ℝ) / (d : ℝ) ^ (n - 1)) =ᶠ[atTop]
        (fun d : ℕ => ((Nat.choose d (n - 1) + 1 : ℕ) : ℝ) / (d : ℝ) ^ (n - 1)) := by
      refine Filter.Eventually.of_forall fun d => ?_
      simp only [Nat.add_zero]
      push_cast
      ring
    rw [tendsto_congr' rewrite] at this
    simpa using this
  have hhigh_lim :
      Tendsto (fun d : ℕ =>
        (((Nat.choose (d + n - 1) (n - 1) + 1 : ℕ)) : ℝ) / (d : ℝ) ^ (n - 1))
        atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) := by
    have h := choose_shift_div_pow_tendsto (n - 1) (n - 1)
    have hsmall : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ (n - 1)) atTop (𝓝 0) := by
      have hpos : 0 < n - 1 := by omega
      have h1 : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun d : ℕ => ((1 : ℝ) / (d : ℝ)) ^ (n - 1)) atTop (𝓝 0) := by
        have := h1.pow (n - 1)
        rwa [zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at this
      refine h2.congr fun d => ?_
      rw [div_pow, one_pow]
    have := h.add hsmall
    have heq : ∀ d, d + (n - 1) = d + n - 1 := fun d => by omega
    have rewrite : (fun d : ℕ => ((Nat.choose (d + (n - 1)) (n - 1) : ℕ) : ℝ) / (d : ℝ) ^ (n - 1)
          + (1 : ℝ) / (d : ℝ) ^ (n - 1)) =ᶠ[atTop]
        (fun d : ℕ => ((Nat.choose (d + n - 1) (n - 1) + 1 : ℕ) : ℝ) / (d : ℝ) ^ (n - 1)) := by
      refine Filter.Eventually.of_forall fun d => ?_
      show (Nat.choose (d + (n - 1)) (n - 1) : ℝ) / (d : ℝ) ^ (n - 1)
            + (1 : ℝ) / (d : ℝ) ^ (n - 1)
          = ((Nat.choose (d + n - 1) (n - 1) + 1 : ℕ) : ℝ) / (d : ℝ) ^ (n - 1)
      rw [heq d]
      push_cast
      ring
    rw [tendsto_congr' rewrite] at this
    simpa using this
  -- Squeeze: lower ≤ gD ≤ upper, both bounds → same limit
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
  · refine Filter.Eventually.of_forall fun d => ?_
    have hge : Nat.choose d (n - 1) + 1 ≤ gD d n :=
      (Nat.add_le_add_right (Nat.choose_le_choose _ d.le_succ) 1).trans (gD_sandwich d n hn).1
    by_cases hd : d = 0
    · subst hd
      have hpos : 0 < n - 1 := by omega
      simp [zero_pow (Nat.pos_iff_ne_zero.mp hpos)]
    · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hpow : (0 : ℝ) < (d : ℝ) ^ (n - 1) := pow_pos hdpos _
      gcongr
  · refine Filter.Eventually.of_forall fun d => ?_
    have hle : gD d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 := (gD_sandwich d n hn).2
    by_cases hd : d = 0
    · subst hd
      have hpos : 0 < n - 1 := by omega
      simp [zero_pow (Nat.pos_iff_ne_zero.mp hpos)]
    · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hpow : (0 : ℝ) < (d : ℝ) ^ (n - 1) := pow_pos hdpos _
      gcongr

/-- **The headline, stated in the problem's own vocabulary.**

`gD_limit` is phrased with `gD`, which this file *defines* as `MD d (n-1) + 1`. This restates it
with `gDSpec`, the literal transcription of Erdős's sentence, so the limit theorem is visibly about
the function the problem names rather than about a convenient reformulation of it. The two are
equal by `gDSpec_eq_gD`; this is the statement to quote when citing the file. -/
theorem gDSpec_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (gDSpec d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 (1 / ((n - 1).factorial : ℝ))) := by
  have h : ∀ d : ℕ, (gDSpec d n : ℝ) / (d : ℝ) ^ (n - 1) = (gD d n : ℝ) / (d : ℝ) ^ (n - 1) := by
    intro d
    rw [gDSpec_eq_gD d n (by omega)]
  simpa only [h] using gD_limit n hn

end ErdosProofs.P1089
