/-
Petrov–Pohoata 2021 (arXiv:1912.08181) formalisation.

Phase 1 of the BBS83 upper bound: the dimension of the subspace of
multivariate polynomials in `d` variables of total degree `≤ s` over a field is
`(d + s choose s)`.
-/

import Mathlib

namespace ErdosProofs.PetrovPohoata

open MvPolynomial Finset

/-! ## Phase 1 — `finrank (restrictTotalDegree (Fin d) K s) = (d+s choose s)` -/

/-- The Finset of all `α : Fin d →₀ ℕ` with `α.sum (· + ·) ≤ s`, presented as a
disjoint biUnion of antidiagonals. -/
def finsuppLE (d s : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.range (s + 1)).biUnion fun i =>
    ((Finset.univ : Finset (Fin d)).finsuppAntidiag i)

theorem mem_finsuppLE {d s : ℕ} {α : Fin d →₀ ℕ} :
    α ∈ finsuppLE d s ↔ α.sum (fun _ e => e) ≤ s := by
  simp only [finsuppLE, Finset.mem_biUnion, Finset.mem_range, mem_finsuppAntidiag']
  constructor
  · rintro ⟨i, hi, hsum, -⟩; rw [hsum]; omega
  · intro h
    refine ⟨α.sum (fun _ e => e), by omega, rfl, ?_⟩
    intro i _; exact Finset.mem_univ i

theorem finsuppAntidiag_pairwise_disjoint (d : ℕ) :
    ∀ i ∈ Finset.range (d.succ), ∀ j ∈ Finset.range (d.succ), i ≠ j →
      Disjoint
        ((Finset.univ : Finset (Fin d)).finsuppAntidiag i)
        ((Finset.univ : Finset (Fin d)).finsuppAntidiag j) := by
  intro i _ j _ hij
  rw [Finset.disjoint_left]
  intro α h1 h2
  rw [mem_finsuppAntidiag'] at h1 h2
  exact hij (h1.1.symm.trans h2.1)

theorem finsuppLE_card (d s : ℕ) :
    (finsuppLE d s).card = Nat.choose (d + s) s := by
  rw [finsuppLE, Finset.card_biUnion]
  · -- ∑ i ∈ range (s+1), #(univ.finsuppAntidiag i) = (d+s).choose s
    have hcard : ∀ i ∈ Finset.range (s + 1),
        ((Finset.univ : Finset (Fin d)).finsuppAntidiag i).card = d.multichoose i := by
      intro i _
      rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_congr rfl hcard]
    rw [Nat.sum_range_multichoose]
    -- (s + d).choose d = (d + s).choose s
    rw [Nat.add_comm s d]
    -- (d + s).choose d = (d + s).choose s
    have h := Nat.choose_symm (Nat.le_add_right d s)
    rw [Nat.add_sub_cancel_left] at h
    exact h.symm
  · -- pairwise disjoint
    intro i _ j _ hij
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro α h1 h2
    rw [mem_finsuppAntidiag'] at h1 h2
    exact hij (h1.1.symm.trans h2.1)

/-- Fintype instance for the subtype of bounded-sum finsupps. -/
instance fintype_finsupp_sum_le (d s : ℕ) :
    Fintype {α : Fin d →₀ ℕ // α.sum (fun _ e => e) ≤ s} where
  elems := (finsuppLE d s).attach.map
    ⟨fun ⟨α, hα⟩ => ⟨α, mem_finsuppLE.mp hα⟩,
     fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext (Subtype.mk.injEq _ _ _ _ |>.mp h)⟩
  complete := by
    rintro ⟨α, hα⟩
    simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists]
    exact ⟨α, mem_finsuppLE.mpr hα, rfl⟩

theorem card_finsupp_sum_le (d s : ℕ) :
    Fintype.card {α : Fin d →₀ ℕ // α.sum (fun _ e => e) ≤ s} = Nat.choose (d + s) s := by
  show ((finsuppLE d s).attach.map _).card = _
  rw [Finset.card_map, Finset.card_attach, finsuppLE_card]

/-- Fintype on the set version (subtype of a Set). -/
instance fintype_finsupp_sum_le_set (d s : ℕ) :
    Fintype ({n : Fin d →₀ ℕ | n.sum (fun _ e => e) ≤ s} : Set _) := by
  exact fintype_finsupp_sum_le d s

theorem card_finsupp_sum_le_set (d s : ℕ) :
    Fintype.card ({n : Fin d →₀ ℕ | n.sum (fun _ e => e) ≤ s} : Set _)
      = Nat.choose (d + s) s :=
  card_finsupp_sum_le d s

/-- The dimension of the subspace of multivariate polynomials in `d` variables
of total degree `≤ s` over a field is `(d + s choose s)`. -/
theorem finrank_restrictTotalDegree (K : Type*) [Field K] (d s : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin d) K s)
      = Nat.choose (d + s) s := by
  -- restrictTotalDegree unfolds to restrictSupport over the bounded-sum set
  unfold MvPolynomial.restrictTotalDegree
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact card_finsupp_sum_le_set d s

/-! ## Phase 2 — `Φ_p` bilinear / quadratic form infrastructure -/

/-- Combine `x` and `y` coordinates into a single `(Fin d) ⊕ (Fin d) → ℝ`. -/
def pair {d : ℕ} (a b : Fin d → ℝ) : Fin d ⊕ Fin d → ℝ := Sum.elim a b

/-- The matrix `M_{p, A}` indexed by `A × A` with entries `p(a, b)`. -/
noncomputable def matrixOfP {d : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) : Matrix A A ℝ :=
  fun a b => MvPolynomial.eval (pair a.val b.val) p

/-- The bilinear form `Φ_p` on `A → ℝ`:
`Φ_p(f, g) = Σ_{a, b ∈ A} p(a, b) · f(a) · g(b)`. -/
noncomputable def phiP {d : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) : LinearMap.BilinForm ℝ (A → ℝ) :=
  Matrix.toBilin'Aux (matrixOfP A p)

/-- The associated quadratic form `f ↦ Φ_p(f, f)`. -/
noncomputable def quadP {d : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) : QuadraticForm ℝ (A → ℝ) :=
  (phiP A p).toQuadraticMap

/-- Explicit double-sum expansion of `Φ_p`. -/
theorem phiP_apply {d : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) (f g : A → ℝ) :
    phiP A p f g = ∑ a, ∑ b, MvPolynomial.eval (pair a.val b.val) p * f a * g b := by
  unfold phiP matrixOfP
  rw [Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, LinearMap.mk₂'ₛₗ_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [smul_eq_mul]
  ring

/-! ## Phase 3 — `Ω`-vanishing

If `f, g : A → ℝ` are orthogonal (under the standard inner product on `A → ℝ`)
to every polynomial of total degree `≤ s` evaluated on `A`, and `p` has total
degree `≤ 2s + 1`, then `Φ_p(f, g) = 0`. -/

/-- `f : A → ℝ` lies in `Ω` iff it is orthogonal to every polynomial of total
degree `≤ s` evaluated on `A`. -/
def InOmega {d : ℕ} (A : Finset (Fin d → ℝ)) (s : ℕ) (f : A → ℝ) : Prop :=
  ∀ φ : MvPolynomial (Fin d) ℝ, φ.totalDegree ≤ s →
    ∑ a, MvPolynomial.eval a.val φ * f a = 0

/-- If `f ∈ Ω` and `α` has degree `≤ s`, the `α`-moment of `f` over `A` vanishes.
This is `InOmega` applied to the monomial `X^α`, with `eval` unfolded to an explicit product. -/
private theorem omega_monomial_sum {d s : ℕ} {A : Finset (Fin d → ℝ)} {f : A → ℝ}
    (hf : InOmega A s f) (α : Fin d →₀ ℕ) (hα : (α.sum fun _ e => e) ≤ s) :
    ∑ a : A, (∏ i, (a.val i) ^ (α i)) * f a = 0 := by
  have hdeg : (MvPolynomial.monomial α (1 : ℝ)).totalDegree ≤ s := by
    rw [MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
    exact hα
  have h := hf _ hdeg
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [MvPolynomial.eval_monomial, one_mul]
  exact (Finsupp.prod_fintype α (fun i e => (a.val i) ^ e) (fun _ => pow_zero _)).symm

/-- The Ω-vanishing lemma (the heart of Theorem 1.2 of Petrov–Pohoata 2021).

For `p` of total degree `≤ 2s + 1` and `f, g ∈ Ω`, `Φ_p(f, g) = 0`.

Proof sketch: expand `p` as a sum of monomials `c · x^α y^β` with
`|α| + |β| ≤ 2s + 1`. For each monomial, at least one of `|α| ≤ s` or
`|β| ≤ s`. WLOG `|α| ≤ s`; then
    `Σ_{a,b} c · a^α · b^β · f(a) · g(b)
        = c · (Σ_a a^α · f(a)) · (Σ_b b^β · g(b))
        = c · 0 · ... = 0`
because `f` is orthogonal to `x^α` (a polynomial of degree `≤ s`). -/
theorem phiP_vanishes_on_Omega {d s : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) (hp : p.totalDegree ≤ 2 * s + 1)
    {f g : A → ℝ} (hf : InOmega A s f) (hg : InOmega A s g) :
    phiP A p f g = 0 := by
  classical
  rw [phiP_apply]
  -- Expand each `p(a, b)` over `p.support`, splitting the `Fin d ⊕ Fin d` product
  -- into its `a`-half and its `b`-half.
  have expand : ∀ a b : A, MvPolynomial.eval (pair a.val b.val) p * f a * g b
      = ∑ m ∈ p.support, MvPolynomial.coeff m p *
          (((∏ i, (a.val i) ^ (m (Sum.inl i))) * f a) *
           ((∏ i, (b.val i) ^ (m (Sum.inr i))) * g b)) := by
    intro a b
    rw [MvPolynomial.eval_eq', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fintype.prod_sum_type]
    simp only [pair, Sum.elim_inl, Sum.elim_inr]
    ring
  simp only [expand]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => Finset.sum_comm), Finset.sum_comm]
  -- The `a`-sum and the `b`-sum separate for each monomial.
  have factor : ∀ (c : ℝ) (X Y : A → ℝ),
      ∑ a : A, ∑ b : A, c * (X a * Y b) = (∑ a : A, X a) * (∑ b : A, c * Y b) := by
    intro c X Y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  refine Finset.sum_eq_zero fun m hm => ?_
  set mL : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inl i)) with hmLdef
  set mR : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inr i)) with hmRdef
  have hmL : ∀ i, mL i = m (Sum.inl i) := fun i => rfl
  have hmR : ∀ i, mR i = m (Sum.inr i) := fun i => rfl
  have hsplit : (mL.sum fun _ e => e) + (mR.sum fun _ e => e) = m.sum fun _ e => e := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
      Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp only [hmL, hmR]
    rw [Fintype.sum_sum_type]
  have hdeg : (m.sum fun _ e => e) ≤ 2 * s + 1 := le_trans (MvPolynomial.le_totalDegree hm) hp
  rw [factor]
  -- `|α| + |β| ≤ 2s + 1` forces one half to have degree `≤ s`; that half's moment vanishes.
  rcases (by omega : (mL.sum fun _ e => e) ≤ s ∨ (mR.sum fun _ e => e) ≤ s) with hle | hle
  · have hz := omega_monomial_sum hf mL hle
    simp only [hmL] at hz
    rw [hz, zero_mul]
  · have hz := omega_monomial_sum hg mR hle
    simp only [hmR] at hz
    rw [← Finset.mul_sum, hz, mul_zero, mul_zero]

/-! ## Phase 4 — Sylvester application

By Sylvester's Law of Inertia, the maximal positive-definite subspace `Y ⊂ A → ℝ`
of `Φ_p` has dimension `r₊ = QuadraticForm.sigPos`. Then `Y ∩ Ω = {0}` (because
`Φ_p` is positive-definite on `Y` but vanishes on `Ω × Ω`), so
    `dim Y + dim Ω ≤ |A|`.
Combined with `dim Ω ≥ |A| − dim_s(A)`, this gives `r₊ ≤ dim_s(A)`. Bounding
`dim_s(A) ≤ dim_s(ℝᵈ) = (d + s choose s)` closes the loop.

Theorem 1.2 part (2) of Petrov–Pohoata: -/

/-- The submodule of `Ω`-functions: orthogonal to all evaluations of polys of
total degree `≤ s` on `A`. -/
def OmegaSubmod {d : ℕ} (A : Finset (Fin d → ℝ)) (s : ℕ) :
    Submodule ℝ (A → ℝ) where
  carrier := {f | InOmega A s f}
  add_mem' := by
    intro f g hf hg φ hφ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hf φ hφ, hg φ hφ, add_zero]
  zero_mem' := by intro φ _; simp
  smul_mem' := by
    intro c f hf φ hφ
    show ∑ a : A, MvPolynomial.eval a.val φ * (c • f) a = 0
    have h_eq : (∑ a : A, MvPolynomial.eval a.val φ * (c • f) a)
              = c * ∑ a : A, MvPolynomial.eval a.val φ * f a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp [smul_eq_mul]; ring
    rw [h_eq, hf φ hφ, mul_zero]

/-- Finite-dimensionality of the degree-`≤ s` subspace, from the Phase 1 basis.

Stated as an instance so that `Subspace.instModuleDualFiniteDimensional` can fire on its dual;
`Module.Finite ℝ (V →ₗ[ℝ] ℝ)` otherwise sends typeclass synthesis into a heartbeat timeout. -/
instance finiteDimensional_restrictTotalDegree (d s : ℕ) :
    FiniteDimensional ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ s) := by
  unfold MvPolynomial.restrictTotalDegree
  exact Module.Basis.finiteDimensional_of_finite (MvPolynomial.basisRestrictSupport ℝ _)

/-- The evaluation pairing `f ↦ (φ ↦ ∑ a ∈ A, φ(a) · f(a))`, as a linear map into the dual of
the degree-`≤ s` subspace. `Ω` is exactly its kernel. -/
noncomputable def evalPairing {d : ℕ} (A : Finset (Fin d → ℝ)) (s : ℕ) :
    (A → ℝ) →ₗ[ℝ] (MvPolynomial.restrictTotalDegree (Fin d) ℝ s →ₗ[ℝ] ℝ) where
  toFun f :=
    { toFun := fun φ => ∑ a : A, MvPolynomial.eval a.val (φ : MvPolynomial (Fin d) ℝ) * f a
      map_add' := by
        intro φ ψ
        simp only [Submodule.coe_add, map_add, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c φ
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum,
          MvPolynomial.smul_eval]
        exact Finset.sum_congr rfl fun a _ => by ring }
  map_add' := by
    intro f g
    ext φ
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c f
    ext φ
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

/-- `Ω` is the kernel of the evaluation pairing. This is just `InOmega`'s definition read
through `restrictTotalDegree`'s membership lemma. -/
theorem OmegaSubmod_eq_ker {d s : ℕ} (A : Finset (Fin d → ℝ)) :
    OmegaSubmod A s = LinearMap.ker (evalPairing A s) := by
  ext f
  simp only [LinearMap.mem_ker]
  constructor
  · intro hf
    ext φ
    have hdeg := φ.2
    rw [MvPolynomial.mem_restrictTotalDegree] at hdeg
    exact hf _ hdeg
  · intro hf φ hφ
    have hmem : φ ∈ MvPolynomial.restrictTotalDegree (Fin d) ℝ s := by
      rw [MvPolynomial.mem_restrictTotalDegree]; exact hφ
    have h := congrArg (fun L => L ⟨φ, hmem⟩) hf
    simpa [evalPairing] using h

/-- The dimension of `Ω` is at least `|A| − (d+s choose s)`.

`Ω = OmegaSubmod A s` is the kernel of `evalPairing A s`. By rank-nullity,
`finrank Ω = |A| - rank pairing ≥ |A| - dim (V*) = |A| - dim V = |A| - (d+s choose s)`. -/
theorem finrank_OmegaSubmod_ge {d s : ℕ} (A : Finset (Fin d → ℝ)) :
    A.card - Nat.choose (d + s) s ≤ Module.finrank ℝ (OmegaSubmod A s) := by
  classical
  rw [OmegaSubmod_eq_ker]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (evalPairing A s)
  have h_src : Module.finrank ℝ (A → ℝ) = A.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  haveI : FiniteDimensional ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ s →ₗ[ℝ] ℝ) :=
    Subspace.instModuleDualFiniteDimensional
  have h_rng_le : Module.finrank ℝ (LinearMap.range (evalPairing A s))
      ≤ Nat.choose (d + s) s := by
    have hdual : Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ s →ₗ[ℝ] ℝ)
        = Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ s) :=
      Subspace.dual_finrank_eq
    refine (Submodule.finrank_le _).trans ?_
    rw [hdual, finrank_restrictTotalDegree]
  rw [h_src] at h_rn
  omega

theorem sigPos_le_choose {d s : ℕ} (A : Finset (Fin d → ℝ))
    (p : MvPolynomial (Fin d ⊕ Fin d) ℝ) (hp : p.totalDegree ≤ 2 * s + 1) :
    sigPos (quadP A p) ≤ Nat.choose (d + s) s := by
  obtain ⟨Y, hY_dim, hY_pos⟩ := exists_finrank_eq_sigPos_and_posDef (quadP A p)
  rw [← hY_dim]
  -- Y ⊓ OmegaSubmod A s = ⊥
  have hYΩ_inf : Y ⊓ OmegaSubmod A s = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨hyY, hyΩ⟩
    by_contra hy_ne
    have hne : (⟨y, hyY⟩ : Y) ≠ 0 := fun h => hy_ne (congr_arg (·.val) h)
    have h_pos := hY_pos ⟨y, hyY⟩ hne
    simp only [QuadraticMap.restrict_apply] at h_pos
    have h_zero : quadP A p y = 0 := phiP_vanishes_on_Omega A p hp hyΩ hyΩ
    linarith
  -- finrank Y + finrank Ω = finrank (Y ⊔ Ω) ≤ |A|
  have hSum := Submodule.finrank_sup_add_finrank_inf_eq Y (OmegaSubmod A s)
  rw [hYΩ_inf, finrank_bot, add_zero] at hSum
  have hSup_le : Module.finrank ℝ (Y ⊔ OmegaSubmod A s : Submodule ℝ (A → ℝ))
      ≤ A.card := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hΩ_ge := finrank_OmegaSubmod_ge (s := s) A
  omega

/-! ## Phase 5 — the witness polynomial -/

/-- The squared L² distance between the `x`- and `y`-coords as a polynomial. -/
noncomputable def distSqPoly (d : ℕ) : MvPolynomial (Fin d ⊕ Fin d) ℝ :=
  ∑ i : Fin d, (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ^ 2

/-- The Aletheia / Petrov–Pohoata witness polynomial:
`∏_{r ∈ S} (r² − ‖x − y‖²)`. -/
noncomputable def sDistanceWitness (d : ℕ) (S : Finset ℝ) :
    MvPolynomial (Fin d ⊕ Fin d) ℝ :=
  ∏ r ∈ S, (MvPolynomial.C (r ^ 2) - distSqPoly d)

/-- `‖x − y‖²` as a polynomial has total degree ≤ 2. -/
theorem distSqPoly_totalDegree (d : ℕ) : (distSqPoly d).totalDegree ≤ 2 := by
  unfold distSqPoly
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i _
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have hX :
      (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)
        : MvPolynomial (Fin d ⊕ Fin d) ℝ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  linarith

/-- The witness polynomial has total degree `≤ 2 |S|`, hence `≤ 2 |S| + 1`. -/
theorem sDistanceWitness_totalDegree (d : ℕ) (S : Finset ℝ) :
    (sDistanceWitness d S).totalDegree ≤ 2 * S.card + 1 := by
  unfold sDistanceWitness
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have h_each : ∀ r ∈ S,
      (MvPolynomial.C (r ^ 2) - distSqPoly d : MvPolynomial _ ℝ).totalDegree ≤ 2 := by
    intro r _
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    exact max_le_iff.mpr ⟨by norm_num, distSqPoly_totalDegree d⟩
  calc ∑ r ∈ S, (MvPolynomial.C (r ^ 2) - distSqPoly d : MvPolynomial _ ℝ).totalDegree
      ≤ ∑ _ ∈ S, 2 := Finset.sum_le_sum h_each
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ 2 * S.card + 1 := Nat.le_succ _

/-! ## Phase 6 — the headline `cardSDistanceSet_le`

The pointwise BBS83 statement: any `s`-distance set in `ℝᵈ` has at most
`(d + s choose s)` points. -/

/-- Diagonal entry of the witness matrix: `M[a, a] = ∏ r∈S, r²`. -/
theorem matrixOfP_witness_diag {d : ℕ} (P : Finset (Fin d → ℝ))
    (S : Finset ℝ) (a : P) :
    matrixOfP P (sDistanceWitness d S) a a = ∏ r ∈ S, r ^ 2 := by
  unfold matrixOfP sDistanceWitness pair distSqPoly
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r _
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_C]
  have h_zero : MvPolynomial.eval (Sum.elim a.val a.val)
      (∑ i : Fin d, (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ^ 2) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X]
    show (a.val i - a.val i) ^ 2 = 0
    ring
  rw [h_zero, sub_zero]

/-- Off-diagonal entry of the witness matrix: `M[a, b] = 0` when `a ≠ b` and the
distances live in `S`. -/
theorem matrixOfP_witness_offdiag {d : ℕ} (P : Finset (Fin d → ℝ)) (S : Finset ℝ)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2)
    (a b : P) (hab : a ≠ b) :
    matrixOfP P (sDistanceWitness d S) a b = 0 := by
  unfold matrixOfP sDistanceWitness pair distSqPoly
  rw [MvPolynomial.eval_prod]
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  obtain ⟨r, hrS, hr⟩ := hSA a.val a.prop b.val b.prop hab'
  apply Finset.prod_eq_zero hrS
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_C]
  have h_dist : MvPolynomial.eval (Sum.elim a.val b.val)
      (∑ i : Fin d, (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ^ 2)
        = ∑ i, (a.val i - b.val i) ^ 2 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X]
    rfl
  rw [h_dist, hr, sub_self]

/-- The quadratic form `Φ_p(f, f)` for the witness `p` reduces to
`(∏ r∈S, r²) · ∑ a, f(a)²`. -/
theorem quadP_witness_apply {d : ℕ} (P : Finset (Fin d → ℝ)) (S : Finset ℝ)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2)
    (f : P → ℝ) :
    quadP P (sDistanceWitness d S) f = (∏ r ∈ S, r ^ 2) * ∑ a, f a ^ 2 := by
  show phiP P (sDistanceWitness d S) f f = _
  rw [phiP_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  -- inner sum: Σ b, M[a,b] * f a * f b → only b = a contributes
  rw [Finset.sum_eq_single a]
  · -- term at b = a: M[a,a] * f a * f a = (∏ r²) * f(a)²
    show MvPolynomial.eval (pair a.val a.val) (sDistanceWitness d S) * f a * f a = _
    rw [show MvPolynomial.eval (pair a.val a.val) (sDistanceWitness d S)
          = matrixOfP P (sDistanceWitness d S) a a from rfl,
      matrixOfP_witness_diag P S a]
    ring
  · -- term at b ≠ a is 0
    intro b _ hba
    show MvPolynomial.eval (pair a.val b.val) (sDistanceWitness d S) * f a * f b = 0
    rw [show MvPolynomial.eval (pair a.val b.val) (sDistanceWitness d S)
          = matrixOfP P (sDistanceWitness d S) a b from rfl,
      matrixOfP_witness_offdiag P S hSA a b (Ne.symm hba)]
    ring
  · intro h; exact absurd (Finset.mem_univ a) h

theorem sigPos_witness_eq_card {d : ℕ} (P : Finset (Fin d → ℝ))
    (S : Finset ℝ) (hS_pos : ∀ r ∈ S, 0 < r)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2) :
    sigPos (quadP P (sDistanceWitness d S)) = P.card := by
  have hdiag_pos : (0 : ℝ) < ∏ r ∈ S, r ^ 2 :=
    Finset.prod_pos fun r hr => pow_pos (hS_pos r hr) 2
  -- PosDef on the whole space
  have hPosDef : (quadP P (sDistanceWitness d S)).PosDef := by
    intro f hf
    rw [quadP_witness_apply P S hSA f]
    apply mul_pos hdiag_pos
    have ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
      by_contra h
      have h' : ∀ a, f a = 0 := fun a => not_not.mp fun ha => h ⟨a, ha⟩
      exact hf (funext h')
    refine Finset.sum_pos' (fun b _ => sq_nonneg (f b)) ⟨a, Finset.mem_univ a, ?_⟩
    exact pow_two_pos_of_ne_zero ha
  -- sigPos = finrank (P → ℝ) via Sylvester (PosDef on top ⇒ sigPos ≥ finrank)
  apply le_antisymm
  · -- sigPos ≤ finrank (P → ℝ) = P.card
    refine (sigPos_le_finrank _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  · -- finrank (P → ℝ) ≤ sigPos via le_sigPos_of_posDef on V = ⊤
    have h := le_sigPos_of_posDef (Q := quadP P (sDistanceWitness d S))
      (V := ⊤) ?_
    · rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h
      simpa using h
    · -- (Q.restrict ⊤).PosDef from Q.PosDef
      intro x hx
      have : (x : P → ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
      exact hPosDef _ this

/-- Pointwise BBS83 in `Fin d → ℝ` flavour. -/
theorem cardSDistanceSet_le_finset {d : ℕ} (P : Finset (Fin d → ℝ))
    (S : Finset ℝ) (hS_pos : ∀ r ∈ S, 0 < r)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2) :
    P.card ≤ Nat.choose (d + S.card) S.card := by
  have h := sigPos_le_choose P (sDistanceWitness d S) (sDistanceWitness_totalDegree d S)
  rw [sigPos_witness_eq_card P S hS_pos hSA] at h
  exact h

/-- BBS83 weakened to `≤ s` distinct distances (rather than `= S` with `S.card`).
This is the form used by `P1089.lean`. -/
theorem cardSDistanceSet_le_finset' {d : ℕ} (s : ℕ) (P : Finset (Fin d → ℝ))
    (S : Finset ℝ) (hS_card : S.card ≤ s) (hS_pos : ∀ r ∈ S, 0 < r)
    (hSA : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      ∃ r ∈ S, (∑ i, (a i - b i) ^ 2 : ℝ) = r ^ 2) :
    P.card ≤ Nat.choose (d + s) s := by
  refine (cardSDistanceSet_le_finset P S hS_pos hSA).trans ?_
  -- (d + #S).choose #S ≤ (d + s).choose s
  -- via choose_symm: (d + k).choose k = (d + k).choose d, then monotonicity in n.
  have h1 : (d + S.card).choose S.card = (d + S.card).choose d := by
    have := Nat.choose_symm (Nat.le_add_left S.card d)
    rw [Nat.add_sub_cancel] at this
    exact this.symm
  have h2 : (d + s).choose s = (d + s).choose d := by
    have := Nat.choose_symm (Nat.le_add_left s d)
    rw [Nat.add_sub_cancel] at this
    exact this.symm
  rw [h1, h2]
  exact Nat.choose_le_choose d (Nat.add_le_add_left hS_card d)

end ErdosProofs.PetrovPohoata
