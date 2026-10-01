import Gaussian.Analysis.HilbertBasisTotality

/-! Parseval with an arbitrary Hilbert-basis index type, for subsequent actual reductions. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Analysis
open scoped InnerProductSpace
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hasSum_hilbert_coeff_norm_sq (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖⟪b i,x⟫_ℂ‖^2) (‖x‖^2) := by
  have h := b.hasSum_inner_mul_inner x x
  have hp (i : ι) : ⟪x,b i⟫_ℂ*⟪b i,x⟫_ℂ=((‖⟪b i,x⟫_ℂ‖^2:ℝ):ℂ) := by
    rw [← inner_conj_symm x (b i),RCLike.conj_mul]
    norm_cast
  have hx : ⟪x,x⟫_ℂ=((‖x‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hp] at h
  rw [hx] at h
  exact Complex.hasSum_ofReal.mp h

end Gaussian.Analysis
