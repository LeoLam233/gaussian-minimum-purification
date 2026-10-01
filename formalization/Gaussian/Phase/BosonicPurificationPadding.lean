import Gaussian.Phase.BosonicPurificationProduct

/-! Exact covariance-only pure-mode padding. Both original forms are retained
in the cost and in the explicit product. No squeezing defect is inverted. -/
noncomputable section
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} (p : PureCompatibleCovariance Ω)
include p

theorem commutator_alternating : Ω.IsAlt := by
  letI : NormedAddCommGroup E := p.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore p.metricCore.toCore
  rw [← p.complexStructure_symplecticForm]
  exact p.complexStructure.symplecticForm_isAlt

theorem commutator_nondegenerate : Ω.Nondegenerate := by
  letI : NormedAddCommGroup E := p.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore p.metricCore.toCore
  rw [← p.complexStructure_symplecticForm]
  exact p.complexStructure.symplecticForm_nondegenerate

/-- A pure covariance has an actual unit Williamson basis, with Ω canonical
and covariance exactly the identity in every mode. -/
theorem exists_unit_canonical_basis {n : ℕ} (hn : finrank ℝ E = 2*n) :
    ∃ b : Basis (Fin n × Bool) ℝ E,
      (∀ i j, Ω (b i) (b j) = canonicalModeSkew n i j) ∧
      (∀ i j, p.form (b i) (b j) = if i=j then 1 else 0) := by
  let d := p.adaptation
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  let b := d.pairedFrame hn
  have ho : ∀ x y, Ω x y = d.complexStructure.symplecticForm x y := by
    intro x y
    exact (congrArg (fun B : LinearMap.BilinForm ℝ E => B x y)
      d.complexStructure_symplecticForm).symm
  refine ⟨b.boolBasis,?_,?_⟩
  · rintro ⟨i,a⟩ ⟨j,c⟩
    simp only [PairedEigenframe.boolBasis,Basis.reindex_apply,OrthonormalBasis.coe_toBasis,
      ho,b.symplectic_matrix]
    cases a <;> cases c <;> simp [finTwoEquiv,canonicalModeMatrix,canonicalModeSkew]
  · intro i j
    change ⟪b.boolBasis i,b.boolBasis j⟫ = if i=j then 1 else 0
    simp only [PairedEigenframe.boolBasis,Basis.reindex_apply,OrthonormalBasis.coe_toBasis,
      b.basis.inner_eq_ite,Equiv.apply_eq_iff_eq]

/-- The independent Hermitian-pair cost of an actual pure covariance is zero. -/
theorem formCost_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℝ E) :
    bosonFormCost e p.form Ω p.symmetric p.commutator_alternating = 0 := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω p.commutator_alternating p.commutator_nondegenerate
  obtain ⟨b,hΩ,hV⟩ := p.exists_unit_canonical_basis (show finrank ℝ E=2*n by omega)
  rw [bosonFormCost_eq_canonical_general e b p.form Ω p.symmetric p.commutator_alternating
    (fun _ => 1) (fun _ => le_rfl) hV hΩ]
  simp

end PureCompatibleCovariance

/-- The actual two-form cost is additive on an explicit covariance product. -/
theorem bosonFormCost_product
    {ι κ η : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [DecidableEq η]
    (V Ω : LinearMap.BilinForm ℝ E) (W σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hW : W.IsSymm) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (hUnc' : Gaussian.Covariance.RealifiedUncertainty W σ)
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) (eProd : Basis η ℝ (E × F)) :
    bosonFormCost eProd (productForm V W) (productForm Ω σ)
      (productForm_symmetric hV hW) (productForm_alternating hΩa hσa) =
      bosonFormCost e V Ω hV hΩa + bosonFormCost f W σ hW hσa := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  obtain ⟨m,hm⟩ := even_finrank_of_nondegenerate_alternating σ hσa hσn
  obtain ⟨ν,b,hν,hbΩ,hbV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn (show finrank ℝ E=2*n by omega) (Gaussian.Covariance.robertson_inequality hUnc)
  obtain ⟨μ,c,hμ,hcσ,hcW⟩ := exists_williamson_basis_bool W σ hW
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc' hσn hx)
    hσa hσn (show finrank ℝ F=2*m by omega) (Gaussian.Covariance.robertson_inequality hUnc')
  let d := (b.prod c).reindex (Equiv.sumProdDistrib (Fin n) (Fin m) Bool).symm
  have hνμ : ∀ i : Fin n ⊕ Fin m, 1 ≤ Sum.elim ν μ i := by
    intro i
    cases i with
    | inl i => exact hν i
    | inr i => exact hμ i
  have hdV : ∀ i j, productForm V W (d i) (d j) =
      if i=j then Sum.elim ν μ i.1 else 0 := by
    rintro ⟨i,a⟩ ⟨j,c'⟩
    cases i <;> cases j <;>
      simp [d,productForm_apply,Basis.prod_apply,hbV,hcW]
  have hdΩ : ∀ i j, productForm Ω σ (d i) (d j) =
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
        else (if j.2 then 1 else 0)) else 0 := by
    rintro ⟨i,a⟩ ⟨j,c'⟩
    cases i <;> cases j <;>
      simp [d,productForm_apply,Basis.prod_apply,hbΩ,hcσ,canonicalModeSkew]
  rw [bosonFormCost_eq_sum_of_mode_basis eProd d (productForm V W) (productForm Ω σ)
    (productForm_symmetric hV hW) (productForm_alternating hΩa hσa)
    (Sum.elim ν μ) hνμ hdV hdΩ,
    bosonFormCost_eq_canonical_general e b V Ω hV hΩa ν hν hbV hbΩ,
    bosonFormCost_eq_canonical_general f c W σ hW hσa μ hμ hcW hcσ]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

/-- Padding by any finite pure covariance preserves the actual two-form cost
exactly, including zero modes and arbitrary pure squeezing. -/
theorem bosonFormCost_pure_padding
    {ι κ η : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [DecidableEq η]
    (V Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (p : PureCompatibleCovariance σ)
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) (eProd : Basis η ℝ (E × F)) :
    bosonFormCost eProd (productForm V p.form) (productForm Ω σ)
      (productForm_symmetric hV p.symmetric) (productForm_alternating hΩa p.commutator_alternating) =
      bosonFormCost e V Ω hV hΩa := by
  rw [bosonFormCost_product V Ω p.form σ hV p.symmetric hΩa p.commutator_alternating
    hΩn p.commutator_nondegenerate hUnc p.uncertainty e f eProd,p.formCost_eq_zero f,add_zero]

end Gaussian.Phase
