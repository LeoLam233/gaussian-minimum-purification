import Gaussian.Physical.Boson.FourierUniqueness

/-! L1 Fourier uniqueness on every finite real configuration space, including dimension zero.
This is the Fourier step of the actual Weyl-kernel injectivity route. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory FourierTransform SchwartzMap
open scoped FourierTransform ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ae_eq_zero_of_fourier_eq_zero_finite {f : E → ℂ} (hf : Integrable f)
    (hzero : 𝓕 f = 0) : ∀ᵐ x, f x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s : 𝓢(E, ℂ) := hgc'.toSchwartzMap hg'
  let t : 𝓢(E, ℂ) := 𝓕⁻ s
  have h : ∫ ξ : E, (𝓕 t) ξ • f ξ = ∫ x : E, t x • (𝓕 f) x := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := volume) (ν := volume) (f := (t : E → ℂ)) (g := f) (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner (t.integrable (μ := volume)) hf)
  simpa [hzero, t, s, Complex.real_smul] using h

end Gaussian.Physical.Boson
