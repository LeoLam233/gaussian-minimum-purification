import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Integrable translated-product correlations, with exact Fubini and L1 estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Correlation without conjugation; conjugates may be included in either input. -/
def correlation (f g : E → ℂ) (q : E) : ℂ := ∫ x, f (x+q) * g x

lemma correlation_eq_convolution (f g : E → ℂ) :
    correlation f g = f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun x => g (-x)) := by
  funext q
  rw [correlation, convolution_def]
  have h := integral_add_right_eq_self (μ := volume) (fun x => f x * g (x-q)) q
  convert h using 1 <;> congr 1 <;> funext x <;> simp

lemma integrable_correlation {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (correlation f g) := by
  rw [correlation_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg.comp_neg

lemma integral_correlation {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ q, correlation f g q) = (∫ x, f x) * (∫ x, g x) := by
  rw [correlation_eq_convolution,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg.comp_neg]
  simp only [ContinuousLinearMap.mul_apply', integral_neg_eq_self]

lemma integral_norm_correlation_le {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ q, ‖correlation f g q‖) ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  let a : E → ℂ := fun x => (‖f x‖ : ℂ)
  let b : E → ℂ := fun x => (‖g x‖ : ℂ)
  have ha : Integrable a := hf.norm.ofReal
  have hb : Integrable b := hg.norm.ofReal
  have hcorr : ∀ q, (correlation a b q).re = ∫ x, ‖f (x+q)‖ * ‖g x‖ := by
    intro q
    simp only [correlation, a, b, ← Complex.ofReal_mul]
    exact congrArg Complex.re (integral_complex_ofReal (f := fun x => ‖f (x+q)‖ * ‖g x‖))
  calc
    _ ≤ ∫ q, (correlation a b q).re := by
      apply integral_mono (integrable_correlation hf hg).norm (integrable_correlation ha hb).re
      intro q
      change ‖correlation f g q‖ ≤ (correlation a b q).re
      rw [hcorr]
      simpa only [correlation, norm_mul] using
        (norm_integral_le_integral_norm (fun x => f (x+q) * g x))
    _ = _ := by
      have hi := integral_re (integrable_correlation ha hb)
      change (∫ q, (correlation a b q).re) = (∫ q, correlation a b q).re at hi
      rw [hi, integral_correlation ha hb]
      simp only [a, b, integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

end Gaussian.Physical.Boson
