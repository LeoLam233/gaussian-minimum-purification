import Gaussian.Physical.Boson.ConfigurationAction

/-! Surjectivity and exact inverse of the normalized real-coordinate action. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem configuration_quasiMeasurePreserving (e : E ≃L[ℝ] E) :
    Measure.QuasiMeasurePreserving e (volume : Measure E) volume := by
  refine ⟨e.continuous.measurable,?_⟩
  rw [configuration_map_volume]
  exact Measure.smul_absolutelyContinuous

theorem configurationJacobian_symm (e : E ≃L[ℝ] E) :
    configurationJacobian e.symm = (configurationJacobian e)⁻¹ := by
  unfold configurationJacobian
  rw [show e.symm.toLinearMap=e.toLinearEquiv.symm.toLinearMap from rfl,
    LinearEquiv.det_coe_symm,abs_inv]

theorem configuration_sqrt_inverse (e : E ≃L[ℝ] E) :
    Real.sqrt (configurationJacobian e.symm)*Real.sqrt (configurationJacobian e)=1 := by
  rw [configurationJacobian_symm,Real.sqrt_inv,inv_mul_cancel₀]
  exact (Real.sqrt_pos.mpr (configurationJacobian_pos e)).ne'

theorem configurationPullback_left_inv (e : E ≃L[ℝ] E) (f : Schrodinger E) :
    configurationPullback e.symm (configurationPullback e f)=f := by
  apply Lp.ext
  have hshift := (configuration_quasiMeasurePreserving e.symm).ae_eq_comp
    (configurationPullback_ae e f)
  filter_upwards [configurationPullback_ae e.symm (configurationPullback e f),hshift] with x h1 h2
  simp only [Function.comp_apply,e.apply_symm_apply] at h2
  rw [h1,h2,← mul_assoc,← Complex.ofReal_mul,configuration_sqrt_inverse,Complex.ofReal_one,one_mul]

def configurationIsometry (e : E ≃L[ℝ] E) : Schrodinger E →ₗᵢ[ℂ] Schrodinger E where
  toFun := configurationPullback e
  map_add' f g := by
    apply Lp.ext
    have ht := (configuration_quasiMeasurePreserving e).ae_eq_comp (Lp.coeFn_add f g)
    filter_upwards [configurationPullback_ae e (f+g),configurationPullback_ae e f,
      configurationPullback_ae e g,ht,
      Lp.coeFn_add (configurationPullback e f) (configurationPullback e g)] with x h1 h2 h3 h4 h5
    simp only [Function.comp_apply,Pi.add_apply] at h4
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,mul_add]
  map_smul' c f := by
    change configurationPullback e (c • f)=c • configurationPullback e f
    apply Lp.ext
    have ht := (configuration_quasiMeasurePreserving e).ae_eq_comp (Lp.coeFn_smul c f)
    filter_upwards [configurationPullback_ae e (c • f),configurationPullback_ae e f,ht,
      Lp.coeFn_smul c (configurationPullback e f)] with x h1 h2 h3 h4
    simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul] at h3
    simp only [h1,h4,Pi.smul_apply,smul_eq_mul,h2,h3,mul_left_comm]
  norm_map' f := by
    change ‖configurationPullback e f‖=‖f‖
    have hi := configurationPullback_inner e f f
    simp only [inner_self_eq_norm_sq_to_K] at hi
    have he : ‖configurationPullback e f‖^2=‖f‖^2 := by exact_mod_cast hi
    nlinarith [norm_nonneg (configurationPullback e f),norm_nonneg f]

def configurationUnitary (e : E ≃L[ℝ] E) : Schrodinger E ≃ₗᵢ[ℂ] Schrodinger E where
  __ := configurationIsometry e
  invFun := configurationPullback e.symm
  left_inv := configurationPullback_left_inv e
  right_inv f := by
    change configurationPullback e (configurationPullback e.symm f)=f
    simpa using configurationPullback_left_inv e.symm f

def configurationOperator (e : E ≃L[ℝ] E) : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  Unitary.linearIsometryEquiv.symm (configurationUnitary e)

end Gaussian.Physical.Boson
