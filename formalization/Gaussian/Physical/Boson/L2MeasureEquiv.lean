import Mathlib.MeasureTheory.Function.L2Space

/-! Actual L² unitary pullback through a proved measure-preserving measurable equivalence. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

theorem l2MeasureEquiv_inverse (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving e.symm he.symm (Lp.compMeasurePreserving e he f)=f := by
  apply Lp.ext
  have ht := he.symm.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving f he)
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e he f) he.symm,ht] with x h1 h2
  simpa only [Function.comp_apply,MeasurableEquiv.apply_symm_apply] using h1.trans h2

def l2MeasureEquiv (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ e he
  invFun := Lp.compMeasurePreserving e.symm he.symm
  left_inv := l2MeasureEquiv_inverse e he
  right_inv f := by
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm he.symm f)=f
    simpa using l2MeasureEquiv_inverse e.symm he.symm f

theorem l2MeasureEquiv_ae (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (f : Lp ℂ 2 ν) :
    l2MeasureEquiv e he f =ᵐ[μ] fun x => f (e x) := Lp.coeFn_compMeasurePreserving f he

end Gaussian.Physical.Boson
