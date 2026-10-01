import Gaussian.Spectral.Interlacing
import Gaussian.Phase.PositiveTools

noncomputable section
open scoped RealInnerProductSpace
namespace Gaussian.Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

theorem eigenvalue_ge_of_quadratic (hK : K.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (c : ℝ)
    (hc : ∀ x, c * ‖x‖^2 ≤ ⟪x,K x⟫) (i : Fin n) : c ≤ hK.eigenvalues hn i := by
  have h := hc (hK.eigenvectorBasis hn i)
  simpa [hK.apply_eigenvectorBasis hn, inner_smul_right, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one] using h

theorem eigenvalue_le_of_quadratic (hK : K.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (c : ℝ)
    (hc : ∀ x, ⟪x,K x⟫ ≤ c * ‖x‖^2) (i : Fin n) : hK.eigenvalues hn i ≤ c := by
  have h := hc (hK.eigenvectorBasis hn i)
  simpa [hK.apply_eigenvectorBasis hn, inner_smul_right, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one] using h

theorem lower_quadratic_of_defect (hK : (K-LinearMap.id).IsPositive) (x : E) :
    1 * ‖x‖^2 ≤ ⟪x,K x⟫ := by
  have h := hK.inner_nonneg_right x
  simp only [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at h
  linarith

theorem upper_quadratic_of_defect (hK : (LinearMap.id-K).IsPositive) (x : E) :
    ⟪x,K x⟫ ≤ 1 * ‖x‖^2 := by
  have h := hK.inner_nonneg_right x
  simp only [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at h
  linarith

theorem compression_lower_quadratic (U : Submodule ℝ E) (c : ℝ)
    (hc : ∀ x, c * ‖x‖^2 ≤ ⟪x,K x⟫) (x : U) :
    c * ‖x‖^2 ≤ ⟪x,compression K U x⟫ := by
  rw [inner_compression]
  exact hc x

theorem compression_upper_quadratic (U : Submodule ℝ E) (c : ℝ)
    (hc : ∀ x, ⟪x,K x⟫ ≤ c * ‖x‖^2) (x : U) :
    ⟪x,compression K U x⟫ ≤ c * ‖x‖^2 := by
  rw [inner_compression]
  exact hc x
end Gaussian.Spectral
