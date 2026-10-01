import Gaussian.Physical.Boson.WeylKernel
import Gaussian.Physical.Boson.Correlation

/-! Schwartz testing of actual nuclear kernel sections, with bounded L1 functionals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory SchwartzMap
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def l1TestFunctional (t : Lp (α := E) ℂ ⊤) : Lp (α := E) ℂ 1 →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 1 1 t)

lemma l1TestFunctional_apply (t : Lp (α := E) ℂ ⊤) (s : Lp (α := E) ℂ 1) :
    l1TestFunctional t s = ∫ x, t x * s x := by
  change L1.integralCLM' ℂ ((ContinuousLinearMap.mul ℂ ℂ).holder 1 t s) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae ((ContinuousLinearMap.mul ℂ ℂ).coeFn_holder t s)

def schwartzTestTop (f g : 𝓢(E,ℂ)) (q : E) : Lp (α := E) ℂ ⊤ :=
  star (Lp.compMeasurePreserving (fun x : E => x+q) (measurePreserving_add_right volume q) (f.toLp ⊤ volume)) • g.toLp ⊤

lemma schwartzTestTop_ae (f g : 𝓢(E,ℂ)) (q : E) :
    schwartzTestTop f g q =ᵐ[volume] fun x => star (f (x+q)) * g x := by
  have hs := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp ⊤)
  filter_upwards [Lp.coeFn_lpSMul (r := ⊤)
      (star (Lp.compMeasurePreserving (fun x : E => x+q) (measurePreserving_add_right volume q) (f.toLp ⊤ volume)))
      (g.toLp ⊤),
    Lp.coeFn_star (Lp.compMeasurePreserving (fun x : E => x+q) (measurePreserving_add_right volume q) (f.toLp ⊤ volume)),
    Lp.coeFn_compMeasurePreserving (f.toLp ⊤) (measurePreserving_add_right volume q),
    hs, g.coeFn_toLp ⊤] with x h1 h2 h3 h4 h5
  change (star (Lp.compMeasurePreserving (fun x : E => x+q) _ (f.toLp ⊤ volume)) • g.toLp ⊤ : Lp (α := E) ℂ ⊤) x = _
  simp only [Function.comp_apply] at h4
  simp only [h1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, h2, Pi.star_apply, h3, Function.comp_apply,
    h4, h5]

lemma test_rankOneSection (f g : 𝓢(E,ℂ)) (u v : Schrodinger E) (q : E) :
    l1TestFunctional (schwartzTestTop f g q) (rankOneSection q u v) =
      correlation (fun x => star (f x) * u x) (fun x => star (v x) * g x) q := by
  rw [l1TestFunctional_apply, correlation]
  apply integral_congr_ae
  filter_upwards [schwartzTestTop_ae f g q, rankOneSection_ae q u v] with x h1 h2
  rw [h1,h2]
  ring

lemma integrable_schwartz_left (f : 𝓢(E,ℂ)) (u : Schrodinger E) :
    Integrable (fun x => star (f x) * u x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (μ := volume) (f.toLp 2 volume) u).congr
  filter_upwards [f.coeFn_toLp 2] with x hx
  simp only [hx, inner, mul_comm]

lemma integrable_schwartz_right (g : 𝓢(E,ℂ)) (v : Schrodinger E) :
    Integrable (fun x => star (v x) * g x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) v (g.toLp 2)).congr
  filter_upwards [g.coeFn_toLp 2] with x hx
  simp only [hx, inner, mul_comm]

lemma integral_schwartz_left (f : 𝓢(E,ℂ)) (u : Schrodinger E) :
    (∫ x, star (f x) * u x) = ⟪f.toLp 2,u⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2] with x hx
  simp only [hx, inner, mul_comm]

lemma integral_schwartz_right (g : 𝓢(E,ℂ)) (v : Schrodinger E) :
    (∫ x, star (v x) * g x) = ⟪v,g.toLp 2⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2] with x hx
  simp only [hx, inner, mul_comm]

lemma integral_norm_schwartz_left_le (f : 𝓢(E,ℂ)) (u : Schrodinger E) :
    (∫ x, ‖star (f x) * u x‖) ≤ ‖f.toLp 2‖ * ‖u‖ := by
  have he : (∫ x, ‖star (f x) * u x‖) = ‖rankOneSection 0 u (f.toLp 2)‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [rankOneSection_ae 0 u (f.toLp 2), f.coeFn_toLp 2] with x h1 h2
    simp only [h1, h2, add_zero, mul_comm]
  rw [he, mul_comm]
  exact norm_rankOneSection_le ..

lemma integral_norm_schwartz_right_le (g : 𝓢(E,ℂ)) (v : Schrodinger E) :
    (∫ x, ‖star (v x) * g x‖) ≤ ‖v‖ * ‖g.toLp 2‖ := by
  have he : (∫ x, ‖star (v x) * g x‖) = ‖rankOneSection 0 (g.toLp 2) v‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [rankOneSection_ae 0 (g.toLp 2) v, g.coeFn_toLp 2] with x h1 h2
    simp only [h1, add_zero, h2, mul_comm]
  rw [he, mul_comm]
  exact norm_rankOneSection_le ..

end Gaussian.Physical.Boson
