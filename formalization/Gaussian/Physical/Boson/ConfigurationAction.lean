import Gaussian.Physical.Boson.WeylImplementation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Determinant-normalized changes of real configuration coordinates on actual
L². Arbitrarily small or large nonzero finite determinants are allowed. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def configurationJacobian (e : E ≃L[ℝ] E) : ℝ := |LinearMap.det e.toLinearMap|

theorem configurationJacobian_pos (e : E ≃L[ℝ] E) : 0<configurationJacobian e :=
  abs_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero

theorem configuration_map_volume (e : E ≃L[ℝ] E) :
    Measure.map e volume = ENNReal.ofReal (configurationJacobian e)⁻¹ • volume := by
  simpa [configurationJacobian,abs_inv] using
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) e.toLinearEquiv.isUnit_det'.ne_zero

theorem configuration_comp_memLp (e : E ≃L[ℝ] E) (f : Schrodinger E) :
    MemLp (fun x => f (e x)) 2 volume := by
  have hf : MemLp f 2 (Measure.map e volume) := by
    rw [configuration_map_volume]
    exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top
  exact hf.comp_of_map e.continuous.measurable.aemeasurable

theorem configuration_weighted_memLp (e : E ≃L[ℝ] E) (f : Schrodinger E) :
    MemLp (fun x => (Real.sqrt (configurationJacobian e):ℂ) * f (e x)) 2 volume := by
  have h := (configuration_comp_memLp e f).const_smul
    (Real.sqrt (configurationJacobian e):ℂ)
  exact h

def configurationPullback (e : E ≃L[ℝ] E) (f : Schrodinger E) : Schrodinger E :=
  (configuration_weighted_memLp e f).toLp _

theorem configurationPullback_ae (e : E ≃L[ℝ] E) (f : Schrodinger E) :
    configurationPullback e f =ᵐ[volume]
      fun x => (Real.sqrt (configurationJacobian e):ℂ) * f (e x) :=
  (configuration_weighted_memLp e f).coeFn_toLp

theorem configuration_integral_comp (e : E ≃L[ℝ] E) (f : E → ℂ) :
    ∫ x, f (e x) = (configurationJacobian e)⁻¹ • ∫ x, f x := by
  have h := e.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure E)) f
  change (∫ x, f x ∂Measure.map e volume) = ∫ x, f (e x) at h
  rw [configuration_map_volume,integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (configurationJacobian_pos e)))] at h
  exact h.symm

theorem configurationPullback_inner (e : E ≃L[ℝ] E) (f g : Schrodinger E) :
    ⟪configurationPullback e f,configurationPullback e g⟫_ℂ=⟪f,g⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ x, (configurationJacobian e:ℂ)*⟪f (e x),g (e x)⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [configurationPullback_ae e f,configurationPullback_ae e g] with x hf hg
      rw [hf,hg]
      change ⟪(Real.sqrt (configurationJacobian e):ℂ) • f (e x),
        (Real.sqrt (configurationJacobian e):ℂ) • g (e x)⟫_ℂ = _
      simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
      have hs : (Real.sqrt (configurationJacobian e):ℂ)^2=(configurationJacobian e:ℂ) := by
        exact_mod_cast Real.sq_sqrt (configurationJacobian_pos e).le
      calc
        _ = ((Real.sqrt (configurationJacobian e):ℂ)^2)*⟪f (e x),g (e x)⟫_ℂ := by ring
        _ = _ := by rw [hs]
    _ = (configurationJacobian e:ℂ)*((configurationJacobian e)⁻¹ • ∫ x,⟪f x,g x⟫_ℂ) := by
      rw [integral_const_mul]
      congr 1
      exact configuration_integral_comp e (fun x => ⟪f x,g x⟫_ℂ)
    _ = ∫ x,⟪f x,g x⟫_ℂ := by
      rw [RCLike.real_smul_eq_coe_mul]
      change (configurationJacobian e:ℂ) * ((((configurationJacobian e)⁻¹:ℝ):ℂ) *
        (∫ x,⟪f x,g x⟫_ℂ)) = ∫ x,⟪f x,g x⟫_ℂ
      rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ (configurationJacobian_pos e).ne',
        Complex.ofReal_one,one_mul]

end Gaussian.Physical.Boson
