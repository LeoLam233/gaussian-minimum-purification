import Gaussian.Physical.Fermion.Purification

/-! Bridge from actual complete-mode marginal equality to the raw physical
subspace compression used by the orthogonal auxiliary-orbit theorem. -/
noncomputable section
open Gaussian.Phase
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- The actual pure density covariance, packaged as an orthogonal complex structure. -/
def pureCovarianceComplexStructure {n : ℕ} (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    OrthogonalComplexStructure (CoefficientSpace n) where
  equiv :=
    { toLinearEquiv :=
        { toLinearMap := covarianceGenerator ρ
          invFun := fun v => -covarianceGenerator ρ v
          left_inv := by
            intro v
            change -covarianceGenerator ρ (covarianceGenerator ρ v) = v
            rw [(quasifree_pure_iff_covariancePure n ρ hρ.1).mp hρ.2,neg_neg]
          right_inv := by
            intro v
            change covarianceGenerator ρ (-covarianceGenerator ρ v) = v
            rw [map_neg,(quasifree_pure_iff_covariancePure n ρ hρ.1).mp hρ.2,neg_neg] }
      norm_map' := skew_square_neg_norm _ (covarianceGenerator_skew ρ)
        ((quasifree_pure_iff_covariancePure n ρ hρ.1).mp hρ.2) }
  square_neg := (quasifree_pure_iff_covariancePure n ρ hρ.1).mp hρ.2

@[simp] theorem pureCovarianceComplexStructure_apply {n : ℕ} (ρ : Density n)
    (hρ : IsPureQuasifree ρ) (v : CoefficientSpace n) :
    pureCovarianceComplexStructure ρ hρ v = covarianceGenerator ρ v := rfl

/-- Retained complete-mode coefficient directions, defined independently of state covariance. -/
def physicalSubspace (k l : ℕ) : Submodule ℝ (CoefficientSpace (l+k)) :=
  Submodule.span ℝ (Set.range (fun a : MajoranaIndex k =>
    coefficientBasis (l+k) (prefixIndex k l a.1,a.2)))

theorem physicalBasis_mem (k l : ℕ) (a : MajoranaIndex k) :
    coefficientBasis (l+k) (prefixIndex k l a.1,a.2) ∈ physicalSubspace k l :=
  Submodule.subset_span ⟨a,rfl⟩

/-- Actual marginal equality forces equality of the left-slot bilinear
covariance compressions on the complete physical coefficient subspace. -/
theorem equal_marginal_physical_compression (k l : ℕ) (ρ σ : Density (l+k))
    (h : prefixRestriction k l ρ = prefixRestriction k l σ)
    (v : CoefficientSpace (l+k)) (hv : v ∈ physicalSubspace k l)
    (w : CoefficientSpace (l+k)) (hw : w ∈ physicalSubspace k l) :
    ⟪covarianceGenerator ρ v,w⟫ = ⟪covarianceGenerator σ v,w⟫ := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => ⟪covarianceGenerator ρ x,y⟫ = ⟪covarianceGenerator σ x,y⟫)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv hw
  · rintro v w ⟨a,rfl⟩ ⟨b,rfl⟩
    rw [covarianceGenerator_inner,covarianceGenerator_inner,covarianceForm_basis,covarianceForm_basis,
      ← prefixRestriction_covariance,← prefixRestriction_covariance,h]
  · intro y hy; simp
  · intro x hx; simp
  · intro x y z hx hy hz h₁ h₂
    simp only [map_add,inner_add_left,h₁,h₂]
  · intro x y z hx hy hz h₁ h₂
    simp only [inner_add_right,h₁,h₂]
  · intro r x y hx hy hxy
    simp only [map_smul,real_inner_smul_left,hxy]
  · intro r x y hx hy hxy
    simp only [real_inner_smul_right,hxy]

/-- A coefficient orthogonal map fixing the physical subspace preserves the
actual density marginal under every one of its CAR unitary implementations. -/
theorem implemented_physicalSubspace_marginal (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (hfix : ∀ v ∈ physicalSubspace k l,R v=v) :
    prefixRestriction k l (ρ.uConj U) = prefixRestriction k l ρ := by
  apply implemented_fixed_prefix_marginal k l ρ R U hU
  intro a
  exact hfix _ (physicalBasis_mem k l a)

end Gaussian.Physical.Fermion
