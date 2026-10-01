import Gaussian.Physical.Boson.FourierWeylFunctions

/-! The actual L² Fourier unitary implements the corresponding scaled
symplectic quarter-turn, including the zero-dimensional configuration space. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory FourierTransform SchwartzMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_weylSchwartz (q p : E) (f : 𝓢(E,ℂ)) :
    𝓕 (weylSchwartz q p f) =
      weylSchwartz (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q) (𝓕 f) := by
  ext y
  rw [weylSchwartz_apply]
  have hc := congrFun (SchwartzMap.fourier_coe (weylSchwartz q p f)) y
  rw [hc]
  have hw : ((weylSchwartz q p f) : E → ℂ) = fun x => phase (weylPhase q p) x*f (x+q) := by
    funext x; exact weylSchwartz_apply q p f x
  rw [hw]
  rw [fourier_weyl_function]
  congr 2
  simp only [sub_eq_add_neg,neg_smul]
  exact (congrFun (SchwartzMap.fourier_coe f) _).symm

theorem fourier_weyl_toLp (q p : E) (f : 𝓢(E,ℂ)) :
    𝓕 (weyl q p (f.toLp 2)) =
      weyl (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q) (𝓕 (f.toLp 2)) := by
  rw [← weylSchwartz_toLp,SchwartzMap.toLp_fourier_eq,fourier_weylSchwartz,
    weylSchwartz_toLp,← SchwartzMap.toLp_fourier_eq]

theorem fourier_weyl_L2 (q p : E) (f : Schrodinger E) :
    𝓕 (weyl q p f) =
      weyl (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q) (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun f : Schrodinger E => 𝓕 (weyl q p f) =
      weyl (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q) (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ E ℂ).continuous.comp (weyl q p).continuous)
      ((weyl (-(2*Real.pi)⁻¹ • p) ((2*Real.pi) • q)).continuous.comp
        (Lp.fourierTransformₗᵢ E ℂ).continuous)
  · intro g
    exact fourier_weyl_toLp q p g

def fourierPhaseMap : (E×E) ≃ₗ[ℝ] (E×E) where
  toFun z := (-(2*Real.pi)⁻¹ • z.2,(2*Real.pi) • z.1)
  invFun z := ((2*Real.pi)⁻¹ • z.2,-(2*Real.pi) • z.1)
  left_inv z := by
    have hc : (2*Real.pi:ℝ)≠0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    ext <;> simp only [smul_smul,neg_mul,neg_neg,mul_neg,
      inv_mul_cancel₀ hc,mul_inv_cancel₀ hc,one_smul]
  right_inv z := by
    have hc : (2*Real.pi:ℝ)≠0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    ext <;> simp only [smul_smul,neg_mul,neg_neg,mul_neg,
      inv_mul_cancel₀ hc,mul_inv_cancel₀ hc,one_smul]
  map_add' z w := by ext <;> simp [smul_add]
  map_smul' c z := by ext <;> simp [smul_smul,mul_comm]

def fourierForwardOperator : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  Unitary.linearIsometryEquiv.symm (Lp.fourierTransformₗᵢ E ℂ)

def fourierInverseOperator : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  star (fourierForwardOperator (E := E))

theorem fourier_implements : WeylImplements (fourierPhaseMap (E := E)) fourierInverseOperator := by
  intro z
  have hi : (fourierForwardOperator (E := E) : Schrodinger E →L[ℂ] Schrodinger E) * weylOperator z.1 z.2 =
      (weylOperator (-(2*Real.pi)⁻¹ • z.2) ((2*Real.pi) • z.1) : Schrodinger E →L[ℂ] Schrodinger E) *
        (fourierForwardOperator (E := E) : Schrodinger E →L[ℂ] Schrodinger E) := by
    apply ContinuousLinearMap.ext
    intro f
    exact fourier_weyl_L2 z.1 z.2 f
  change star (star (fourierForwardOperator (E := E) : Schrodinger E →L[ℂ] Schrodinger E)) *
    weylOperator z.1 z.2 * star (fourierForwardOperator (E := E) : Schrodinger E →L[ℂ] Schrodinger E) = _
  rw [star_star,hi,mul_assoc,Unitary.mul_star_self_of_mem (fourierForwardOperator (E := E)).property,mul_one]
  rfl

theorem fourierPhaseMap_symplectic (z w : E×E) :
    weylSymplecticForm E (fourierPhaseMap z) (fourierPhaseMap w)=weylSymplecticForm E z w := by
  change ⟪-(2*Real.pi)⁻¹ • z.2,(2*Real.pi) • w.1⟫ -
    ⟪(2*Real.pi) • z.1,-(2*Real.pi)⁻¹ • w.2⟫ = _
  simp only [inner_smul_left,inner_smul_right,conj_trivial,weylSymplecticForm_apply]
  field_simp [Real.pi_ne_zero]
  ring

end Gaussian.Physical.Boson
