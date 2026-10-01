import Gaussian.Physical.Boson.WeylImplementation
import Mathlib.Analysis.Fourier.LpSpace

/-! Exact Weyl/Fourier intertwining on concrete functions, with the pinned
Fourier convention exp(-2πi〈x,y〉). The L² extension is a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory FourierTransform SchwartzMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_weyl_phase (q p x y : E) :
    Complex.exp ((-2*Real.pi*⟪x,y⟫:ℝ)*Complex.I)*phase (weylPhase q p) x =
      phase (weylPhase (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q)) y *
        Complex.exp ((-2*Real.pi*⟪x+q,y-(2*Real.pi)⁻¹ • p⟫:ℝ)*Complex.I) := by
  unfold phase weylPhase
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [inner_add_left,inner_sub_right,inner_smul_left,inner_smul_right,
    conj_trivial,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [real_inner_comm p x,real_inner_comm p q]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem fourier_weyl_function (q p : E) (f : E → ℂ) (y : E) :
    𝓕 (fun x => phase (weylPhase q p) x * f (x+q)) y =
      phase (weylPhase (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q)) y *
        𝓕 f (y-(2*Real.pi)⁻¹ • p) := by
  rw [Real.fourier_eq',Real.fourier_eq',← integral_const_mul]
  simp only [smul_eq_mul]
  calc
    _ = ∫ x, phase (weylPhase (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q)) y *
        (Complex.exp ((-2*Real.pi*⟪x+q,y-(2*Real.pi)⁻¹ • p⟫:ℝ)*Complex.I)*f (x+q)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← mul_assoc,fourier_weyl_phase,mul_assoc]
    _ = _ := integral_add_right_eq_self (μ := (volume : Measure E))
      (fun x => phase (weylPhase (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q)) y *
        (Complex.exp ((-2*Real.pi*⟪x,y-(2*Real.pi)⁻¹ • p⟫:ℝ)*Complex.I)*f x)) q

theorem weylPhase_hasTemperateGrowth (q p : E) :
    (phase (weylPhase q p)).HasTemperateGrowth := by
  unfold phase weylPhase
  apply Complex.hasTemperateGrowth_exp_mul_I.comp
  have hp := (innerSL ℝ p).hasTemperateGrowth
  exact hp.add (Function.HasTemperateGrowth.const _)

def weylSchwartz (q p : E) (f : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (phase (weylPhase q p)) (f.compSubConstCLM ℂ (-q))

@[simp] theorem weylSchwartz_apply (q p : E) (f : 𝓢(E,ℂ)) (x : E) :
    weylSchwartz q p f x=phase (weylPhase q p) x*f (x+q) := by
  simp [weylSchwartz,SchwartzMap.smulLeftCLM_apply_apply (weylPhase_hasTemperateGrowth q p)]

theorem weylSchwartz_toLp (q p : E) (f : 𝓢(E,ℂ)) :
    (weylSchwartz q p f).toLp 2=weyl q p (f.toLp 2) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2)
  filter_upwards [(weylSchwartz q p f).coeFn_toLp 2,weyl_ae q p (f.toLp 2),ht] with x h1 h2 h3
  simp only [Function.comp_apply] at h3
  rw [h1,h2,weylSchwartz_apply,h3]

end Gaussian.Physical.Boson
