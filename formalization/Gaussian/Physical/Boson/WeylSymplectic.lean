import Gaussian.Physical.Boson.GaussianPredicate
import Gaussian.Physical.Boson.WeylGram

set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual real commutator form from the proved Schrödinger Weyl cocycle. -/
def weylSymplecticForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    LinearMap.BilinForm ℝ (E×E) :=
  (innerₗ E).compl₁₂ (LinearMap.fst ℝ E E) (LinearMap.snd ℝ E E) -
    (innerₗ E).compl₁₂ (LinearMap.snd ℝ E E) (LinearMap.fst ℝ E E)

@[simp] theorem weylSymplecticForm_apply (z w : E×E) :
    weylSymplecticForm E z w=⟪z.1,w.2⟫-⟪z.2,w.1⟫ := rfl

theorem weylSymplecticForm_swap (z w : E×E) :
    weylSymplecticForm E z w= -weylSymplecticForm E w z := by
  simp only [weylSymplecticForm_apply]
  rw [real_inner_comm w.1 z.2,real_inner_comm w.2 z.1]
  ring

theorem weylSymplecticForm_isAlt : (weylSymplecticForm E).IsAlt := by
  intro z
  simp only [weylSymplecticForm_apply]
  exact sub_eq_zero.mpr (real_inner_comm _ _)

theorem weylSymplecticForm_nondegenerate : (weylSymplecticForm E).Nondegenerate := by
  have hl : ∀ z : E×E,(∀ w,weylSymplecticForm E z w=0) → z=0 := by
    intro z hz
    have hq := hz (0,z.1)
    have hp := hz (z.2,0)
    simp only [weylSymplecticForm_apply,inner_zero_right,sub_zero,zero_sub,neg_eq_zero] at hq hp
    apply Prod.ext
    · exact inner_self_eq_zero.mp hq
    · exact inner_self_eq_zero.mp hp
  refine ⟨hl,?_⟩
  intro z hz
  apply hl z
  intro w
  rw [weylSymplecticForm_swap,hz w,neg_zero]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weylCocycle_negative_first (z w : E×E) :
    weylCocycle (-z.1) (-z.2) w.1 w.2 =
      Complex.exp (-(weylSymplecticForm E z w : ℂ)/2*Complex.I) := by
  unfold weylCocycle
  simp only [inner_neg_left,inner_neg_right,weylSymplecticForm_apply]
  rw [real_inner_comm w.2 z.1]
  congr 1
  push_cast
  ring

theorem centered_expect_weyl {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E×E)} (h : IsGaussianWith ρ 0 V) (z : E×E) :
    ρ.expect (weylOperator z.1 z.2)=(Real.exp (-V z z/4):ℂ) := by
  change ρ.characteristic z.1 z.2=_
  simpa [neg_div] using h.2 z.1 z.2

theorem centered_expect_star_weyl {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E×E)} (h : IsGaussianWith ρ 0 V) (z : E×E) :
    ρ.expect (star (weylOperator z.1 z.2 : Schrodinger E →L[ℂ] Schrodinger E))=
      (Real.exp (-V z z/4):ℂ) := by
  rw [weylOperator_star]
  have hh := centered_expect_weyl h (-z)
  simpa using hh

theorem centered_expect_star_weyl_mul {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E×E)} (h : IsGaussianWith ρ 0 V) (z w : E×E) :
    ρ.expect (star (weylOperator z.1 z.2 : Schrodinger E →L[ℂ] Schrodinger E)*
      (weylOperator w.1 w.2 : Schrodinger E →L[ℂ] Schrodinger E)) =
      Complex.exp (-(V (w-z) (w-z):ℂ)/4-(weylSymplecticForm E z w:ℂ)/2*Complex.I) := by
  rw [weylOperator_star,weylOperator_mul,ρ.expect_smul,weylCocycle_negative_first z w]
  have hq : -z.1+w.1=(w-z).1 := by simp [sub_eq_add_neg,add_comm]
  have hp : -z.2+w.2=(w-z).2 := by simp [sub_eq_add_neg,add_comm]
  rw [hq,hp,centered_expect_weyl h,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

end Gaussian.Physical.Boson
