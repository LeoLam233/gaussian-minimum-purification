import Gaussian.Physical.Fermion.PrefixCoefficient
import Gaussian.Physical.Fermion.ModeSelection
import Gaussian.Physical.Fermion.SuffixRestriction

/-! Constructed orthogonal lift of a local complete-mode cut transformation.
The untouched suffix is fixed as a CAR subsystem, including odd orthogonal
components; no ordinary unsigned tensor-unitary identification is assumed. -/
noncomputable section
namespace Gaussian.Physical.Fermion

@[simp] theorem blockMajoranaEquiv_suffix (k l : ℕ) (a : MajoranaIndex l) :
    blockMajoranaEquiv k l (Sum.inr a)=(suffixIndex k l a.1,a.2) := by
  apply Prod.ext
  · apply Fin.ext
    change k+a.1.val=(suffixIndex k l a.1).val
    rw [suffixIndex_val]
  · rfl

/-- The coefficient decomposition uses the true Euclidean L² product. -/
def cutCoefficientSplit (k l : ℕ) : CoefficientSpace (l+k) ≃ₗᵢ[ℝ]
    WithLp 2 (CoefficientSpace k × CoefficientSpace l) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockMajoranaEquiv k l).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : MajoranaIndex k ⊕ MajoranaIndex l => ℝ))

theorem sumCoefficient_single_inl (k l : ℕ) (a : MajoranaIndex k) :
    PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : MajoranaIndex k ⊕ MajoranaIndex l => ℝ)
      (EuclideanSpace.single (Sum.inl a) 1) =
      WithLp.toLp 2 (coefficientBasis k a,(0 : CoefficientSpace l)) := by
  apply (WithLp.linearEquiv 2 ℝ (CoefficientSpace k × CoefficientSpace l)).injective
  apply Prod.ext
  · ext b
    change (EuclideanSpace.single (Sum.inl a) (1:ℝ) : EuclideanSpace ℝ (MajoranaIndex k ⊕ MajoranaIndex l))
      (Sum.inl b) = coefficientBasis k a b
    simp [coefficientBasis,PiLp.single_apply]
  · ext b
    change (EuclideanSpace.single (Sum.inl a) (1:ℝ) : EuclideanSpace ℝ (MajoranaIndex k ⊕ MajoranaIndex l))
      (Sum.inr b) = 0
    simp [PiLp.single_apply]

theorem sumCoefficient_single_inr (k l : ℕ) (a : MajoranaIndex l) :
    PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : MajoranaIndex k ⊕ MajoranaIndex l => ℝ)
      (EuclideanSpace.single (Sum.inr a) 1) =
      WithLp.toLp 2 ((0 : CoefficientSpace k),coefficientBasis l a) := by
  apply (WithLp.linearEquiv 2 ℝ (CoefficientSpace k × CoefficientSpace l)).injective
  apply Prod.ext
  · ext b
    change (EuclideanSpace.single (Sum.inr a) (1:ℝ) : EuclideanSpace ℝ (MajoranaIndex k ⊕ MajoranaIndex l))
      (Sum.inl b) = 0
    simp [PiLp.single_apply]
  · ext b
    change (EuclideanSpace.single (Sum.inr a) (1:ℝ) : EuclideanSpace ℝ (MajoranaIndex k ⊕ MajoranaIndex l))
      (Sum.inr b) = coefficientBasis l a b
    simp [coefficientBasis,PiLp.single_apply]

@[simp] theorem cutCoefficientSplit_prefix_basis (k l : ℕ) (a : MajoranaIndex k) :
    cutCoefficientSplit k l (coefficientBasis (l+k) (prefixIndex k l a.1,a.2)) =
      WithLp.toLp 2 (coefficientBasis k a,(0 : CoefficientSpace l)) := by
  rw [← blockMajoranaEquiv_inl k l a]
  simp only [cutCoefficientSplit,LinearIsometryEquiv.trans_apply,coefficientBasis,
    reindexCoefficient_single,Equiv.symm_apply_apply]
  exact sumCoefficient_single_inl k l a

@[simp] theorem cutCoefficientSplit_suffix_basis (k l : ℕ) (a : MajoranaIndex l) :
    cutCoefficientSplit k l (coefficientBasis (l+k) (suffixIndex k l a.1,a.2)) =
      WithLp.toLp 2 ((0 : CoefficientSpace k),coefficientBasis l a) := by
  rw [← blockMajoranaEquiv_suffix k l a]
  simp only [cutCoefficientSplit,LinearIsometryEquiv.trans_apply,coefficientBasis,
    reindexCoefficient_single,Equiv.symm_apply_apply]
  exact sumCoefficient_single_inr k l a

@[simp] theorem cutCoefficientSplit_prefix (k l : ℕ) (v : CoefficientSpace k) :
    cutCoefficientSplit k l (prefixCoefficientEmbedding k l v) = WithLp.toLp 2 (v,(0 : CoefficientSpace l)) := by
  let L := (WithLp.linearEquiv 2 ℝ (CoefficientSpace k × CoefficientSpace l)).symm.toLinearMap.comp
    (LinearMap.inl ℝ (CoefficientSpace k) (CoefficientSpace l))
  have he : (cutCoefficientSplit k l).toLinearEquiv.toLinearMap.comp
      (prefixCoefficientEmbedding k l).toLinearMap = L := by
    apply (EuclideanSpace.basisFun (MajoranaIndex k) ℝ).toBasis.ext
    intro a
    simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    change cutCoefficientSplit k l (prefixCoefficientEmbedding k l (coefficientBasis k a)) =
      WithLp.toLp 2 (coefficientBasis k a,(0 : CoefficientSpace l))
    rw [prefixCoefficientEmbedding_basis]
    exact cutCoefficientSplit_prefix_basis k l a
  exact LinearMap.congr_fun he v

/-- Local orthogonal action on the prefix and identity on its Euclidean complement. -/
def localCutLift (k l : ℕ) (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) :
    CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k) :=
  (cutCoefficientSplit k l).trans
    ((LinearIsometryEquiv.withLpProdCongr (p := 2) R
      (LinearIsometryEquiv.refl ℝ (CoefficientSpace l))).trans (cutCoefficientSplit k l).symm)

@[simp] theorem localCutLift_prefix (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) (v : CoefficientSpace k) :
    localCutLift k l R (prefixCoefficientEmbedding k l v) = prefixCoefficientEmbedding k l (R v) := by
  apply (cutCoefficientSplit k l).injective
  simp only [localCutLift,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,
    cutCoefficientSplit_prefix]
  rfl

@[simp] theorem localCutLift_suffix_basis (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) (a : MajoranaIndex l) :
    localCutLift k l R (coefficientBasis (l+k) (suffixIndex k l a.1,a.2)) =
      coefficientBasis (l+k) (suffixIndex k l a.1,a.2) := by
  apply (cutCoefficientSplit k l).injective
  simp only [localCutLift,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,
    cutCoefficientSplit_suffix_basis]
  change WithLp.toLp 2 (R 0,coefficientBasis l a) = WithLp.toLp 2 (0,coefficientBasis l a)
  rw [map_zero]

theorem localCutLift_prefix_fixed (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) (a : MajoranaIndex k)
    (ha : R (coefficientBasis k a)=coefficientBasis k a) :
    localCutLift k l R (coefficientBasis (l+k) (prefixIndex k l a.1,a.2)) =
      coefficientBasis (l+k) (prefixIndex k l a.1,a.2) := by
  change localCutLift k l R (coefficientBasis (l+k) (prefixMajoranaIndex k l a)) =
    coefficientBasis (l+k) (prefixMajoranaIndex k l a)
  rw [← prefixCoefficientEmbedding_basis k l a,localCutLift_prefix,ha]

theorem localCutLift_inverse_prefix (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) (v : CoefficientSpace k) :
    (localCutLift k l R)⁻¹ (prefixCoefficientEmbedding k l v) =
      prefixCoefficientEmbedding k l (R⁻¹ v) := by
  apply (localCutLift k l R).injective
  simp only [LinearIsometryEquiv.inv_def,LinearIsometryEquiv.apply_symm_apply,localCutLift_prefix]

theorem localCutLift_inverse_suffix_basis (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k) (a : MajoranaIndex l) :
    (localCutLift k l R)⁻¹ (coefficientBasis (l+k) (suffixIndex k l a.1,a.2)) =
      coefficientBasis (l+k) (suffixIndex k l a.1,a.2) := by
  apply (localCutLift k l R).injective
  simp only [LinearIsometryEquiv.inv_def,LinearIsometryEquiv.apply_symm_apply,localCutLift_suffix_basis]

/-- The lifted actual state action has exactly the specified local prefix action. -/
theorem localCutLift_prefix_density (k l : ℕ) (ρ : Density (l+k)) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (U : Matrix.unitaryGroup (Occupation k) ℂ) (hU : Implements k R U)
    (V : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hV : Implements (l+k) (localCutLift k l R) V) :
    prefixRestriction k l (ρ.uConj V) = (prefixRestriction k l ρ).uConj U := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_orthogonalRestriction k l ρ hρ _ V hV)
    (isQuasifree_unitary_of_implements k _ (isQuasifree_prefixRestriction k l ρ hρ) R U hU)
  intro a b
  rw [← covarianceForm_basis,← covarianceForm_basis,orthogonalRestriction_covarianceForm k l ρ _ V hV,
    implemented_covarianceForm _ R U hU,prefixRestriction_covarianceForm,
    localCutLift_inverse_prefix,localCutLift_inverse_prefix]

/-- The complementary density is unchanged as an actual signed CAR subsystem. -/
theorem localCutLift_suffix_density (k l : ℕ) (ρ : Density (l+k)) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (V : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hV : Implements (l+k) (localCutLift k l R) V) :
    suffixRestriction k l (ρ.uConj V) = suffixRestriction k l ρ := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_suffixRestriction k l _ (isQuasifree_unitary_of_implements (l+k) ρ hρ _ V hV))
    (isQuasifree_suffixRestriction k l ρ hρ)
  intro a b
  rw [suffixRestriction_covariance,suffixRestriction_covariance,← covarianceForm_basis,
    implemented_covarianceForm ρ _ V hV,localCutLift_inverse_suffix_basis,localCutLift_inverse_suffix_basis,
    covarianceForm_basis]

/-- Every local orthogonal action admits a genuinely implemented global lift. -/
theorem exists_localCutLift_action (k l : ℕ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (U : Matrix.unitaryGroup (Occupation k) ℂ) (hU : Implements k R U) :
    ∃ V : Matrix.unitaryGroup (Occupation (l+k)) ℂ,Implements (l+k) (localCutLift k l R) V ∧
      ∀ ρ : Density (l+k),IsQuasifree ρ →
        prefixRestriction k l (ρ.uConj V)=(prefixRestriction k l ρ).uConj U ∧
        suffixRestriction k l (ρ.uConj V)=suffixRestriction k l ρ := by
  obtain ⟨V,hV⟩ := orthogonal_implemented (l+k) (localCutLift k l R)
  exact ⟨V,hV,fun ρ hρ => ⟨localCutLift_prefix_density k l ρ hρ R U hU V hV,
    localCutLift_suffix_density k l ρ hρ R V hV⟩⟩

end Gaussian.Physical.Fermion
