import Gaussian.Physical.Boson.ConfigurationUnitary

/-! Exact Schrödinger implementation of the configuration/contragredient
symplectic transformation, with the actual determinant-normalized unitary. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem adjoint_inverse_left (e : E ≃L[ℝ] E) (x : E) :
    e.toContinuousLinearMap.adjoint (e.symm.toContinuousLinearMap.adjoint x)=x := by
  change (e.toContinuousLinearMap.adjoint.comp e.symm.toContinuousLinearMap.adjoint) x=x
  rw [← ContinuousLinearMap.adjoint_comp]
  have he : e.symm.toContinuousLinearMap.comp e.toContinuousLinearMap=ContinuousLinearMap.id ℝ E := by
    ext y
    exact e.symm_apply_apply y
  rw [he,ContinuousLinearMap.adjoint_id]
  rfl

def configurationContragredient (e : E ≃L[ℝ] E) : E ≃ₗ[ℝ] E where
  __ := e.symm.toContinuousLinearMap.adjoint.toLinearMap
  invFun := e.toContinuousLinearMap.adjoint
  left_inv := adjoint_inverse_left e
  right_inv x := by simpa using adjoint_inverse_left e.symm x

def configurationPhaseMap (e : E ≃L[ℝ] E) : (E×E) ≃ₗ[ℝ] (E×E) :=
  e.toLinearEquiv.prodCongr (configurationContragredient e)

@[simp] theorem configurationPhaseMap_apply (e : E ≃L[ℝ] E) (z : E×E) :
    configurationPhaseMap e z = (e z.1,e.symm.toContinuousLinearMap.adjoint z.2) := rfl

theorem configuration_phase_identity (e : E ≃L[ℝ] E) (q p x : E) :
    weylPhase (e q) (e.symm.toContinuousLinearMap.adjoint p) (e x)=weylPhase q p x := by
  unfold weylPhase
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  simp

theorem configuration_intertwine (e : E ≃L[ℝ] E) (q p : E) (f : Schrodinger E) :
    weyl q p (configurationUnitary e f) =
      configurationUnitary e (weyl (e q) (e.symm.toContinuousLinearMap.adjoint p) f) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (configurationPullback_ae e f)
  have he := (configuration_quasiMeasurePreserving e).ae_eq_comp
    (weyl_ae (e q) (e.symm.toContinuousLinearMap.adjoint p) f)
  filter_upwards [weyl_ae q p (configurationUnitary e f),ht,he,
    configurationPullback_ae e (weyl (e q) (e.symm.toContinuousLinearMap.adjoint p) f)] with x h1 h2 h3 h4
  change configurationUnitary e f (x+q) =
    (Real.sqrt (configurationJacobian e):ℂ) * f (e (x+q)) at h2
  change weyl (e q) (e.symm.toContinuousLinearMap.adjoint p) f (e x) =
    phase (weylPhase (e q) (e.symm.toContinuousLinearMap.adjoint p)) (e x)*f (e x+e q) at h3
  change configurationUnitary e (weyl (e q) (e.symm.toContinuousLinearMap.adjoint p) f) x = _ at h4
  rw [h1,h2,h4,h3,map_add]
  unfold phase
  rw [configuration_phase_identity]
  ring

theorem configuration_implements (e : E ≃L[ℝ] E) :
    WeylImplements (configurationPhaseMap e) (configurationOperator e) := by
  intro z
  have hi : (weylOperator z.1 z.2 : Schrodinger E →L[ℂ] Schrodinger E)*configurationOperator e =
      (configurationOperator e : Schrodinger E →L[ℂ] Schrodinger E)*
        weylOperator (e z.1) (e.symm.toContinuousLinearMap.adjoint z.2) := by
    apply ContinuousLinearMap.ext
    intro f
    exact configuration_intertwine e z.1 z.2 f
  rw [mul_assoc,hi,← mul_assoc,Unitary.star_mul_self_of_mem (configurationOperator e).property,one_mul]
  rfl

theorem configurationPhaseMap_symplectic (e : E ≃L[ℝ] E) (z w : E×E) :
    weylSymplecticForm E (configurationPhaseMap e z) (configurationPhaseMap e w)=
      weylSymplecticForm E z w := by
  simp only [weylSymplecticForm_apply,configurationPhaseMap_apply]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_left]
  simp

end Gaussian.Physical.Boson
