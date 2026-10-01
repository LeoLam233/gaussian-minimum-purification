import Gaussian.Physical.Fermion.ThermalGenerator
import Gaussian.Physical.Fermion.NormalFormBridge
import Gaussian.Phase.PairedFrame

/-! The actual physical covariance is adapted and put into paired normal form.
The orthogonal frame and admissible thermal parameters are constructed from the
raw density; no normal-form data are assumed in the final existence theorem. -/
noncomputable section
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace BigOperators
namespace Gaussian.Physical.Fermion

variable {n : ℕ}
variable {J : OrthogonalComplexStructure (CoefficientSpace n)}
variable {K : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n}

def boolFrame (b : PairedEigenframe J K n) : OrthonormalBasis (MajoranaIndex n) ℝ (CoefficientSpace n) :=
  b.basis.reindex (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv)

@[simp] theorem boolFrame_false (b : PairedEigenframe J K n) (i : Fin n) :
    boolFrame b (i,false) = b.basis (i,0) := by
  simp [boolFrame,OrthonormalBasis.reindex_apply,finTwoEquiv]

@[simp] theorem boolFrame_true (b : PairedEigenframe J K n) (i : Fin n) :
    boolFrame b (i,true) = b.basis (i,1) := by
  simp [boolFrame,OrthonormalBasis.reindex_apply,finTwoEquiv]

/-- The actual orthogonal map taking standard complete modes to the constructed frame. -/
def frameRotation (b : PairedEigenframe J K n) : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n :=
  (EuclideanSpace.basisFun (MajoranaIndex n) ℝ).equiv (boolFrame b) (Equiv.refl _)

@[simp] theorem frameRotation_basis (b : PairedEigenframe J K n) (a : MajoranaIndex n) :
    frameRotation b (coefficientBasis n a) = boolFrame b a := by
  unfold frameRotation coefficientBasis
  rw [← EuclideanSpace.basisFun_apply]
  exact OrthonormalBasis.equiv_apply_basis _ _ _ a

theorem pairedGenerator_false (ρ : Density n) (b : PairedEigenframe J K n)
    (hT : ∀ x, covarianceGenerator ρ x = J (K x)) (i : Fin n) :
    covarianceGenerator ρ (boolFrame b (i,false)) = b.value i • boolFrame b (i,true) := by
  rw [boolFrame_false,boolFrame_true,hT,b.eigen,J.apply_smul,b.partner]

theorem pairedGenerator_true (ρ : Density n) (b : PairedEigenframe J K n)
    (hT : ∀ x, covarianceGenerator ρ x = J (K x)) (i : Fin n) :
    covarianceGenerator ρ (boolFrame b (i,true)) = -b.value i • boolFrame b (i,false) := by
  rw [boolFrame_false,boolFrame_true,hT,b.eigen,J.apply_smul,b.partner_second]
  simp

/-- Both raw real skew generators are intertwined by the actual orthogonal frame. -/
theorem frameRotation_intertwine (ρ : Density n) (b : PairedEigenframe J K n)
    (hT : ∀ x, covarianceGenerator ρ x = J (K x))
    (ht : ∀ i, b.value i ∈ Set.Icc (-1:ℝ) 1) (v : CoefficientSpace n) :
    covarianceGenerator ρ (frameRotation b v) =
      frameRotation b (covarianceGenerator (thermal n b.value ht) v) := by
  have hL : (covarianceGenerator ρ).comp (frameRotation b).toLinearEquiv.toLinearMap =
      (frameRotation b).toLinearEquiv.toLinearMap.comp (covarianceGenerator (thermal n b.value ht)) := by
    apply (EuclideanSpace.basisFun (MajoranaIndex n) ℝ).toBasis.ext
    intro a
    simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    change covarianceGenerator ρ (frameRotation b (coefficientBasis n a)) =
      frameRotation b (covarianceGenerator (thermal n b.value ht) (coefficientBasis n a))
    rw [frameRotation_basis]
    rcases a with ⟨i,k⟩
    cases k
    · rw [pairedGenerator_false ρ b hT,thermalGenerator_false,map_smul,frameRotation_basis]
    · rw [pairedGenerator_true ρ b hT,thermalGenerator_true,map_smul,frameRotation_basis]
  exact congrArg (fun L : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n => L v) hL

theorem frameRotation_covarianceForm (ρ : Density n) (b : PairedEigenframe J K n)
    (hT : ∀ x, covarianceGenerator ρ x = J (K x))
    (ht : ∀ i, b.value i ∈ Set.Icc (-1:ℝ) 1) (v w : CoefficientSpace n) :
    covarianceForm ρ (frameRotation b v) (frameRotation b w) =
      covarianceForm (thermal n b.value ht) v w := by
  rw [← covarianceGenerator_inner,frameRotation_intertwine ρ b hT ht,
    (frameRotation b).inner_map_map,covarianceGenerator_inner]

/-- The actual density produces its own admissible paired covariance normal form. -/
theorem exists_physical_covariance_normal_form (n : ℕ) (ρ : Density n) :
    ∃ (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
      (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n),
      (∀ i, 0 ≤ t i) ∧ ∀ a b, covariance ρ a b = covarianceForm (thermal n t ht)
        (R⁻¹ (coefficientBasis n a)) (R⁻¹ (coefficientBasis n b)) := by
  have hd : finrank ℝ (CoefficientSpace n) = 2*n := by
    simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
  have he : Even (finrank ℝ (CoefficientSpace n)) := ⟨n,by omega⟩
  obtain ⟨d⟩ := exists_skewAdaptation (covarianceGenerator ρ) (covarianceGenerator_skew ρ) he
  obtain ⟨b⟩ := exists_pairedEigenframe_dim n (CoefficientSpace n) hd
    d.complexStructure d.K d.positive.isSymmetric d.commute
  have hlo (i : Fin n) : 0 ≤ b.value i := by
    apply b.value_ge 0
    intro x
    simpa only [zero_mul] using d.positive.inner_nonneg_right x
  have hhi (i : Fin n) : b.value i ≤ 1 := by
    have h := (d.one_sub_positive (covarianceGenerator_contraction ρ)).inner_nonneg_left
      (b.basis (i,0))
    change 0 ≤ ⟪b.basis (i,0)-d.K (b.basis (i,0)),b.basis (i,0)⟫ at h
    rw [b.eigen,inner_sub_left,real_inner_smul_left,b.basis.inner_eq_ite] at h
    simpa using h
  let ht : ∀ i, b.value i ∈ Set.Icc (-1:ℝ) 1 := fun i => ⟨by linarith [hlo i],hhi i⟩
  refine ⟨b.value,ht,frameRotation b,hlo,?_⟩
  intro a c
  have h := frameRotation_covarianceForm ρ b d.factor ht
    ((frameRotation b).symm (coefficientBasis n a)) ((frameRotation b).symm (coefficientBasis n c))
  simpa only [LinearIsometryEquiv.apply_symm_apply,covarianceForm_basis,
    LinearIsometryEquiv.inv_def] using h

/-- Every raw finite parity-invariant Wick density is an actual orthogonal image
of a canonical thermal density, with all parameters constructed from its covariance. -/
theorem exists_quasifree_state_normal_form (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    ∃ (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
      (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
      (U : Matrix.unitaryGroup (Occupation n) ℂ),
      (∀ i,0 ≤ t i) ∧ Implements n R U ∧ ρ = (thermal n t ht).uConj U := by
  obtain ⟨t,ht,R,hpos,hΓ⟩ := exists_physical_covariance_normal_form n ρ
  obtain ⟨U,hU⟩ := orthogonal_implemented n R
  exact ⟨t,ht,R,U,hpos,hU,quasifree_eq_rotated_thermal_of_covariance n ρ hρ t ht R U hU hΓ⟩

end Gaussian.Physical.Fermion
