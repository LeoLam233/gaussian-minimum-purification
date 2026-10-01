import Gaussian.Physical.Boson.NormalDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Concrete unitary multiplication by exp(iθ(x)) on untruncated L2. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def phase (θ : α → ℝ) (x : α) : ℂ := Complex.exp ((θ x : ℂ) * Complex.I)

omit [MeasurableSpace α] in
@[simp] theorem norm_phase (θ : α → ℝ) (x : α) : ‖phase θ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_memLp (θ : α → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    MemLp (fun x => phase θ x * f x) 2 μ := by
  apply (Lp.memLp f).congr_norm
  · exact ((Complex.continuous_exp.measurable.comp
      (hθ.complex_ofReal.mul measurable_const)).aestronglyMeasurable).mul (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with x
    simp only [norm_mul, norm_phase, one_mul]

def phaseMultiply (θ : α → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (phase_memLp θ hθ f).toLp _

theorem phaseMultiply_ae (θ : α → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    phaseMultiply θ hθ f =ᵐ[μ] fun x => phase θ x * f x :=
  (phase_memLp θ hθ f).coeFn_toLp

@[simp] theorem phaseMultiply_norm (θ : α → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    ‖phaseMultiply θ hθ f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [phaseMultiply_ae θ hθ f] with x hx
    rw [hx, norm_mul, norm_phase, one_mul]
  · filter_upwards [phaseMultiply_ae θ hθ f] with x hx
    rw [hx, norm_mul, norm_phase, one_mul]

def phaseIsometry (θ : α → ℝ) (hθ : Measurable θ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := phaseMultiply θ hθ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [phaseMultiply_ae θ hθ (f+g), phaseMultiply_ae θ hθ f,
      phaseMultiply_ae θ hθ g, Lp.coeFn_add f g,
      Lp.coeFn_add (phaseMultiply θ hθ f) (phaseMultiply θ hθ g)] with x h1 h2 h3 h4 h5
    simp only [h1, h5, Pi.add_apply, h2, h3, h4, mul_add]
  map_smul' c f := by
    change phaseMultiply θ hθ (c • f) = c • phaseMultiply θ hθ f
    apply Lp.ext
    filter_upwards [phaseMultiply_ae θ hθ (c • f), phaseMultiply_ae θ hθ f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseMultiply θ hθ f)] with x h1 h2 h3 h4
    simp only [h1, h4, h2, h3, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  norm_map' := phaseMultiply_norm θ hθ

theorem phaseMultiply_neg_left (θ : α → ℝ) (hθ : Measurable θ) (f : Lp ℂ 2 μ) :
    phaseMultiply (-θ) hθ.neg (phaseMultiply θ hθ f) = f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_ae (-θ) hθ.neg (phaseMultiply θ hθ f),
    phaseMultiply_ae θ hθ f] with x h1 h2
  rw [h1, h2, ← mul_assoc]
  simp [phase, ← Complex.exp_add]

def phaseUnitary (θ : α → ℝ) (hθ : Measurable θ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := phaseIsometry θ hθ
  invFun := phaseMultiply (-θ) hθ.neg
  left_inv := phaseMultiply_neg_left θ hθ
  right_inv f := by
    change phaseMultiply θ hθ (phaseMultiply (-θ) hθ.neg f) = f
    simpa only [neg_neg] using phaseMultiply_neg_left (-θ) hθ.neg f

end Gaussian.Physical.Boson
