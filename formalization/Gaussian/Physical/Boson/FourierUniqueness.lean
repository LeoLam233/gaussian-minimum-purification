import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! L1 Fourier uniqueness, used to bypass the conditional Plancherel premise in oscillator completeness. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory FourierTransform SchwartzMap
open scoped FourierTransform ContDiff

theorem ae_eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hzero : 𝓕 f = 0) : ∀ᵐ x, f x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hg'
  let t : 𝓢(ℝ, ℂ) := 𝓕⁻ s
  have h : ∫ ξ : ℝ, (𝓕 t) ξ • f ξ = ∫ x : ℝ, t x • (𝓕 f) x := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := volume) (ν := volume) (f := (t : ℝ → ℂ)) (g := f) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (t.integrable (μ := volume)) hf)
  simpa [hzero, t, s, Complex.real_smul] using h

end Gaussian.Physical.Boson
