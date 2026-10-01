import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine pointwise product vectors in L² of a product measure. These are
analytic Hilbert-space facts, not a postulated tensor interpretation. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem productVector_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : α×β => f z.1*g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd)).mpr
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  simpa only [Pi.mul_apply,norm_mul,mul_pow] using hf.mul_prod hg

def productVector (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (productVector_memLp f g).toLp _

theorem productVector_ae (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productVector f g =ᵐ[μ.prod ν] fun z => f z.1*g z.2 :=
  (productVector_memLp f g).coeFn_toLp

theorem productVector_inner (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    ⟪productVector f g,productVector f' g'⟫_ℂ=⟪f,f'⟫_ℂ*⟪g,g'⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def]
  calc
    _ = ∫ z, ⟪f z.1,f' z.1⟫_ℂ*⟪g z.2,g' z.2⟫_ℂ ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [productVector_ae f g,productVector_ae f' g'] with z h1 h2
      rw [h1,h2]
      simp only [RCLike.inner_apply,map_mul]
      ring
    _ = _ := integral_prod_mul (μ := μ) (ν := ν)
      (fun x : α => ⟪f x,f' x⟫_ℂ) (fun y : β => ⟪g y,g' y⟫_ℂ)

theorem productVector_norm (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖productVector f g‖=‖f‖*‖g‖ := by
  have hi := productVector_inner f f g g
  simp only [inner_self_eq_norm_sq_to_K] at hi
  have hr : ‖productVector f g‖^2=‖f‖^2*‖g‖^2 := by exact_mod_cast hi
  nlinarith [norm_nonneg (productVector f g),mul_nonneg (norm_nonneg f) (norm_nonneg g)]

end Gaussian.Physical.Boson
