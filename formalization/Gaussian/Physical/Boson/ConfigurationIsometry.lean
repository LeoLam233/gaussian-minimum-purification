import Gaussian.Physical.Boson.L2MeasureEquiv
import Gaussian.Physical.Boson.Weyl

/-! Actual Schrödinger pullback under a real configuration isometry, including different
finite configuration types. The actual Weyl operators intertwine without a determinant factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped RealInnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def schrodingerIsometry (e : E ≃ₗᵢ[ℝ] F) : Schrodinger E ≃ₗᵢ[ℂ] Schrodinger F :=
  l2MeasureEquiv e.symm.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv e.symm.measurePreserving

lemma schrodingerIsometry_ae (e : E ≃ₗᵢ[ℝ] F) (f : Schrodinger E) :
    schrodingerIsometry e f =ᵐ[volume] fun x => f (e.symm x) :=
  l2MeasureEquiv_ae _ _ f

lemma isometry_weylPhase (e : E ≃ₗᵢ[ℝ] F) (q p : E) (x : F) :
    weylPhase (e q) (e p) x=weylPhase q p (e.symm x) := by
  have h : ⟪e p,x⟫=⟪p,e.symm x⟫ := by
    simpa only [e.apply_symm_apply] using e.inner_map_map p (e.symm x)
  simp only [weylPhase,h,e.inner_map_map]

/-- Intertwining is equality of actual untruncated L² vectors. -/
theorem schrodingerIsometry_weyl (e : E ≃ₗᵢ[ℝ] F) (q p : E) (f : Schrodinger E) :
    schrodingerIsometry e (weyl q p f)=weyl (e q) (e p) (schrodingerIsometry e f) := by
  apply Lp.ext
  have hw := e.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp (weyl_ae q p f)
  have hs := (measurePreserving_add_right volume (e q)).quasiMeasurePreserving.ae_eq_comp
    (schrodingerIsometry_ae e f)
  filter_upwards [schrodingerIsometry_ae e (weyl q p f),hw,
    weyl_ae (e q) (e p) (schrodingerIsometry e f),hs] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2 h4
  rw [h1,h2,h3,h4,map_add,e.symm_apply_apply]
  rw [show phase (weylPhase (e q) (e p)) x=phase (weylPhase q p) (e.symm x) from
    congrArg (fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I)) (isometry_weylPhase e q p x)]

end Gaussian.Physical.Boson
