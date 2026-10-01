import Gaussian.Physical.Fermion.RawRealization
import Gaussian.Physical.Fermion.ThermalPurity

/-! Covariance purity is equivalent to actual pure-state admissibility for the
raw finite CAR Wick domain; zero mode counts and both parity components remain. -/
noncomputable section
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

def CovariancePure {n : ℕ} (ρ : Density n) : Prop :=
  ∀ v,covarianceGenerator ρ (covarianceGenerator ρ v) = -v

theorem thermal_covariancePure_iff_endpoints (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    CovariancePure (thermal n t ht) ↔ ∀ i,t i=1 ∨ t i = -1 := by
  constructor
  · intro h i
    have he := h (coefficientBasis n (i,false))
    rw [thermalGenerator_false,map_smul,thermalGenerator_true,smul_smul] at he
    have hs := congrArg (fun v : CoefficientSpace n => v (i,false)) he
    simp [coefficientBasis,PiLp.single_apply,PiLp.smul_apply] at hs
    rcases le_or_gt 0 (t i) with hi | hi
    · left; nlinarith
    · right; nlinarith
  · intro he
    have hL : (covarianceGenerator (thermal n t ht)).comp (covarianceGenerator (thermal n t ht)) =
        -LinearMap.id := by
      apply (EuclideanSpace.basisFun (MajoranaIndex n) ℝ).toBasis.ext
      intro a
      simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
      change covarianceGenerator (thermal n t ht) (covarianceGenerator (thermal n t ht)
        (coefficientBasis n a)) = -coefficientBasis n a
      rcases a with ⟨i,b⟩
      cases b
      · rw [thermalGenerator_false,map_smul,thermalGenerator_true,smul_smul]
        rcases he i with h | h <;> simp [h]
      · rw [thermalGenerator_true,map_smul,thermalGenerator_false,smul_smul]
        rcases he i with h | h <;> simp [h]
    intro v
    exact congrArg (fun L : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n => L v) hL

theorem implemented_covariancePure_iff {n : ℕ} (ρ : Density n)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    CovariancePure (ρ.uConj U) ↔ CovariancePure ρ := by
  constructor
  · intro h v
    have he := h (R v)
    rw [implemented_generator_intertwine ρ R U hU,implemented_generator_intertwine ρ R U hU] at he
    apply R.injective
    rw [map_neg]
    exact he
  · intro h w
    obtain ⟨v,rfl⟩ := R.surjective w
    rw [implemented_generator_intertwine ρ R U hU,implemented_generator_intertwine ρ R U hU,h,map_neg]

/-- Actual density purity is exactly polynomial covariance purity for every raw Wick state. -/
theorem quasifree_pure_iff_covariancePure (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    (∃ ψ,ρ=MState.pure ψ) ↔ CovariancePure ρ := by
  obtain ⟨t,ht,R,U,hpos,hU,he⟩ := exists_quasifree_state_normal_form n ρ hρ
  rw [he,unitaryState_pure_iff,implemented_covariancePure_iff _ R U hU,
    thermal_pure_iff_endpoints,thermal_covariancePure_iff_endpoints]

/-- A raw real skew square root of minus identity is automatically a contraction. -/
theorem skew_square_neg_norm {n : ℕ} (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n)
    (hT : IsSkew T) (hPure : ∀ v,T (T v) = -v) (v : CoefficientSpace n) : ‖T v‖=‖v‖ := by
  have h : ⟪T v,T v⟫ = ⟪v,v⟫ := by rw [hT,hPure,inner_neg_right,neg_neg]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Pure raw covariance data are realized by an actual pure quasifree state. -/
theorem realize_pure_skew (n : ℕ) (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n)
    (hT : IsSkew T) (hPure : ∀ v,T (T v) = -v) :
    ∃ ρ : Density n,IsPureQuasifree ρ ∧ covarianceGenerator ρ=T := by
  obtain ⟨ρ,hρ,hΓ⟩ := realize_skew_contraction n T hT
    (fun v => (skew_square_neg_norm T hT hPure v).le)
  refine ⟨ρ,⟨hρ,?_⟩,hΓ⟩
  apply (quasifree_pure_iff_covariancePure n ρ hρ).mpr
  intro v
  rw [hΓ,hPure]

end Gaussian.Physical.Fermion
