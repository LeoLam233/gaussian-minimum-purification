import Gaussian.Physical.Fermion.CoefficientMatrices
import Gaussian.Physical.Fermion.ThermalSpectrum
import Gaussian.Physical.Fermion.GaussianClosure

/-! Full actual-state entropy versus independent Hermitian covariance CFC cost.
Real orthogonal coefficient changes are complexified through proved inverse
identities; characteristic-polynomial eigenbasis transport preserves the cost. -/
noncomputable section
open Module Gaussian.Spectral
open scoped Matrix RealInnerProductSpace BigOperators
namespace Gaussian.Physical.Fermion

/-- Physical covariance transport intertwines the actual left-slot real generators. -/
theorem implemented_generator_intertwine {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) (v : CoefficientSpace n) :
    covarianceGenerator (ρ.uConj U) (R v) = R (covarianceGenerator ρ v) := by
  apply ext_inner_right ℝ
  intro w
  calc
    ⟪covarianceGenerator (ρ.uConj U) (R v),w⟫ = covarianceForm (ρ.uConj U) (R v) w :=
      covarianceGenerator_inner _ _ _
    _ = covarianceForm ρ v (R.symm w) := by
      rw [implemented_covarianceForm ρ R U hU]
      simp only [LinearIsometryEquiv.inv_def,LinearIsometryEquiv.symm_apply_apply]
    _ = ⟪covarianceGenerator ρ v,R.symm w⟫ := (covarianceGenerator_inner _ _ _).symm
    _ = ⟪R (covarianceGenerator ρ v),w⟫ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (R.inner_map_map (covarianceGenerator ρ v) (R.symm w)).symm

def generatorMatrix {n : ℕ} (ρ : Density n) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  fun a b => -covariance ρ a b

@[simp] theorem toEuclidean_generatorMatrix {n : ℕ} (ρ : Density n) :
    Matrix.toEuclideanLin (generatorMatrix ρ) = covarianceGenerator ρ := rfl

theorem implemented_generatorMatrix_intertwine {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    generatorMatrix (ρ.uConj U)*coefficientMatrix R = coefficientMatrix R*generatorMatrix ρ := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,toEuclidean_generatorMatrix,coefficientMatrix_toEuclidean]
  apply LinearMap.ext
  intro v
  exact implemented_generator_intertwine ρ R U hU v

theorem hermitianCovariance_eq_generatorMatrix {n : ℕ} (ρ : Density n) :
    hermitianCovariance ρ = (-Complex.I) • complexifyMatrix (generatorMatrix ρ) := by
  ext a b
  simp [hermitianCovariance,generatorMatrix,complexifyMatrix]

theorem implemented_hermitian_intertwine {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    hermitianCovariance (ρ.uConj U)*complexifyMatrix (coefficientMatrix R) =
      complexifyMatrix (coefficientMatrix R)*hermitianCovariance ρ := by
  have h := congrArg complexifyMatrix (implemented_generatorMatrix_intertwine ρ R U hU)
  simp only [complexifyMatrix_mul] at h
  rw [hermitianCovariance_eq_generatorMatrix,hermitianCovariance_eq_generatorMatrix,
    Matrix.smul_mul,Matrix.mul_smul,h]

theorem implemented_covariance_eigenvector {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U)
    (v : MajoranaIndex n → ℂ) (a : ℝ)
    (hv : hermitianCovariance ρ*ᵥv = (a:ℂ) • v) :
    hermitianCovariance (ρ.uConj U)*ᵥcomplexCoefficientEquiv R v =
      (a:ℂ) • complexCoefficientEquiv R v := by
  rw [complexCoefficientEquiv_apply,Matrix.mulVec_mulVec,
    implemented_hermitian_intertwine ρ R U hU,← Matrix.mulVec_mulVec,hv,Matrix.mulVec_smul]

/-- All covariance trace-CFC functions are preserved by the actual physical
orthogonal transformation, proved from an independent complex eigenbasis. -/
theorem implemented_covariance_trace_cfc {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) (f : ℝ → ℝ) :
    ((covarianceHermitianMat (ρ.uConj U)).cfc f).trace = ((covarianceHermitianMat ρ).cfc f).trace := by
  let H := covarianceHermitianMat ρ
  let b : Basis (MajoranaIndex n) ℂ (MajoranaIndex n → ℂ) :=
    H.H.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℂ (MajoranaIndex n → ℂ))
  have hb (i : MajoranaIndex n) : hermitianCovariance ρ*ᵥb i = (H.H.eigenvalues i : ℂ) • b i := by
    exact H.H.mulVec_eigenvectorBasis i
  let c := b.map (complexCoefficientEquiv R)
  have hc (i : MajoranaIndex n) :
      hermitianCovariance (ρ.uConj U)*ᵥc i = (H.H.eigenvalues i : ℂ) • c i := by
    exact implemented_covariance_eigenvector ρ R U hU (b i) (H.H.eigenvalues i) (hb i)
  rw [hermitian_trace_cfc_eq_eigenbasis_sum (covarianceHermitianMat (ρ.uConj U)) c
    H.H.eigenvalues hc f,HermitianMat.trace_cfc_eq]

/-- Actual von Neumann entropy of every raw finite CAR quasifree density equals
the independently defined Hermitian covariance spectral cost. -/
theorem quasifree_entropy_eq_hermitianCost (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    Sᵥₙ ρ = Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat ρ) := by
  obtain ⟨t,ht,R,U,hpos,hU,he⟩ := exists_quasifree_state_normal_form n ρ hρ
  calc
    Sᵥₙ ρ = Sᵥₙ (thermal n t ht) := by rw [he,unitaryState_entropy]
    _ = Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat (thermal n t ht)) := by
      rw [entropy_thermal,thermal_hermitianCost]
    _ = Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat ρ) := by
      rw [he]
      unfold Gaussian.Attainment.fermionHermitianCost
      rw [implemented_covariance_trace_cfc _ R U hU]

end Gaussian.Physical.Fermion
