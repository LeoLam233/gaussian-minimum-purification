import Gaussian.Physical.Boson.ChirpAction
import Gaussian.Physical.Boson.FourierAction
import Gaussian.Physical.Boson.WeylComposition

/-! Concrete implementation of every symmetric upper shear by Fourier/chirp/Fourier inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def upperShear (S : E →L[ℝ] E) : (E×E) ≃ₗ[ℝ] (E×E) where
  toFun z := (z.1+S z.2,z.2)
  invFun z := (z.1-S z.2,z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp <;> abel
  map_smul' c z := by ext <;> simp [smul_add]

@[simp] lemma upperShear_apply (S : E →L[ℝ] E) (z : E×E) :
    upperShear S z = (z.1+S z.2,z.2) := rfl

lemma upperShear_eq_fourier (S : E →L[ℝ] E) :
    upperShear S = ((fourierPhaseMap (E := E)).trans
      (chirpShear ((-((2*Real.pi)^2)) • S))).trans fourierPhaseMap.symm := by
  have hc : (2*Real.pi:ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  apply LinearEquiv.ext
  intro z
  apply Prod.ext
  · change z.1+S z.2 = (2*Real.pi)⁻¹ •
      ((2*Real.pi) • z.1 + ((-((2*Real.pi)^2)) • S) (-(2*Real.pi)⁻¹ • z.2))
    simp only [ContinuousLinearMap.smul_apply,map_smul,smul_add,smul_smul]
    have h1 : (2*Real.pi)⁻¹*(2*Real.pi)=1 := inv_mul_cancel₀ hc
    have h2 : (2*Real.pi)⁻¹*(-(2*Real.pi)⁻¹*(-((2*Real.pi)^2)))=1 := by
      field_simp
    simp only [h1,h2,one_smul]
  · change z.2 = -(2*Real.pi) • (-(2*Real.pi)⁻¹ • z.2)
    simp only [smul_smul,neg_mul_neg,mul_inv_cancel₀ hc,one_smul]

def upperShearOperator (S : E →L[ℝ] E) : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  (fourierInverseOperator * chirpOperator ((-((2*Real.pi)^2)) • S)) * star fourierInverseOperator

/-- No bound is imposed on the shear coefficient. -/
theorem upperShear_implements (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) :
    WeylImplements (upperShear S) (upperShearOperator S) := by
  have hT : ∀ x y, ⟪((-((2*Real.pi)^2)) • S) x,y⟫ =
      ⟪x,((-((2*Real.pi)^2)) • S) y⟫ := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply,inner_smul_left,inner_smul_right,conj_trivial,hS]
  rw [upperShear_eq_fourier]
  exact (fourier_implements.trans (chirp_implements _ hT)).trans fourier_implements.symm

theorem upperShear_symplectic (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) (z w : E×E) :
    weylSymplecticForm E (upperShear S z) (upperShear S w)=weylSymplecticForm E z w := by
  simp only [weylSymplecticForm_apply,upperShear_apply,inner_add_left,inner_add_right,hS]
  ring

end Gaussian.Physical.Boson
