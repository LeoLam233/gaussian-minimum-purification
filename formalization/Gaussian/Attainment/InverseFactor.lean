import Gaussian.Attainment.HermitianBounds
import Gaussian.Attainment.Coercivity

/-! Exact inverse-form factorization behind bosonic sublevel coercivity. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Gaussian.Attainment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual inverse commutator factor is recovered from the independently
constructed Hermitian pair matrix; both form and covariance remain in the identity. -/
theorem bosonPair_inverse_factor (V O : HermitianMat ι ℂ) (hV : V.mat.PosDef) :
    O.mat⁻¹ = -(V.sqrt.mat⁻¹ * (bosonPairHermitian V O).mat * V.sqrt.mat⁻¹) := by
  have hS : IsUnit V.sqrt.mat.det := isUnit_iff_ne_zero.mpr (HermitianMat.sqrt_posDef hV).det_pos.ne'
  have hleft := Matrix.nonsing_inv_mul V.sqrt.mat hS
  have hright := Matrix.mul_nonsing_inv V.sqrt.mat hS
  have he : V.sqrt.mat⁻¹ * (bosonPairHermitian V O).mat * V.sqrt.mat⁻¹ = -O.mat⁻¹ := by
    simp only [bosonPairHermitian, HermitianMat.conj_apply_mat,
      HermitianMat.mat_neg, HermitianMat.mat_inv, HermitianMat.conjTranspose_mat]
    calc
      V.sqrt.mat⁻¹ * (V.sqrt.mat * -O.mat⁻¹ * V.sqrt.mat) * V.sqrt.mat⁻¹ =
        (V.sqrt.mat⁻¹ * V.sqrt.mat) * -O.mat⁻¹ * (V.sqrt.mat * V.sqrt.mat⁻¹) := by simp [mul_assoc]
      _ = -O.mat⁻¹ := by rw [hleft,hright,one_mul,mul_one]
  rw [he,neg_neg]

/-- This inequality is in the induced Euclidean Hilbert operator norm. -/
theorem bosonPair_inverse_norm (V O : HermitianMat ι ℂ) (hV : V.mat.PosDef) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) O.mat⁻¹‖ ≤
      ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V.sqrt.mat⁻¹‖ ^ 2 *
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (bosonPairHermitian V O).mat‖ := by
  let Φ := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  rw [bosonPair_inverse_factor V O hV, map_neg, norm_neg, map_mul, map_mul]
  calc
    ‖(Φ V.sqrt.mat⁻¹ * Φ (bosonPairHermitian V O).mat) * Φ V.sqrt.mat⁻¹‖ ≤
        (‖Φ V.sqrt.mat⁻¹‖ * ‖Φ (bosonPairHermitian V O).mat‖) * ‖Φ V.sqrt.mat⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by ring
end Gaussian.Attainment
