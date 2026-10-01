import Gaussian.Physical.Fermion.LinearMajorana
import Gaussian.LinearAlgebra.OrthogonalGeneration

noncomputable section
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

@[simp] theorem linearMajorana_sub (n : ℕ) (v w : CoefficientSpace n) :
    linearMajorana n (v-w) = linearMajorana n v - linearMajorana n w := by
  simp [sub_eq_add_neg]

theorem unitMajorana_conjugate (n : ℕ) (v w : CoefficientSpace n) (hv : ‖v‖ = 1) :
    linearMajorana n v * linearMajorana n w * linearMajorana n v =
      linearMajorana n (((2 : ℝ) * ⟪v,w⟫) • v - w) := by
  have hsq : linearMajorana n v * linearMajorana n v = 1 := by
    rw [linearMajorana_square, hv]; simp
  rw [eq_sub_of_add_eq (linearMajorana_car n v w), Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hsq, Matrix.mul_one,
    linearMajorana_sub, linearMajorana_smul]
  simp

def parityUnitary (n : ℕ) : Matrix.unitaryGroup (Occupation n) ℂ :=
  ⟨parity n, by rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    parity_hermitian, parity_square]⟩

def unitMajoranaUnitary (n : ℕ) (v : CoefficientSpace n) (hv : ‖v‖=1) :
    Matrix.unitaryGroup (Occupation n) ℂ :=
  ⟨linearMajorana n v, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      linearMajorana_hermitian, linearMajorana_square, hv]
    simp⟩

theorem parity_conjugate_linearMajorana (n : ℕ) (v : CoefficientSpace n) :
    parity n * linearMajorana n v * parity n = -linearMajorana n v := by
  rw [(neg_eq_iff_eq_neg.mpr (linearMajorana_parity n v)).symm,
    Matrix.neg_mul, Matrix.mul_assoc, parity_square, Matrix.mul_one]

def Implements (n : ℕ) (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) : Prop :=
  ∀ v, (U : Operator n) * linearMajorana n v * (U : Operator n)ᴴ = linearMajorana n (R v)

theorem unit_reflection_implemented (n : ℕ) (v : CoefficientSpace n) (hv : ‖v‖=1) :
    Implements n (Gaussian.LinearAlgebra.hyperplaneReflection v)
      (parityUnitary n * unitMajoranaUnitary n v hv) := by
  intro w
  change (parity n * linearMajorana n v) * linearMajorana n w *
    (parity n * linearMajorana n v)ᴴ = _
  rw [Matrix.conjTranspose_mul, linearMajorana_hermitian, parity_hermitian]
  calc
    (parity n * linearMajorana n v) * linearMajorana n w *
        (linearMajorana n v * parity n) =
      parity n * (linearMajorana n v * linearMajorana n w * linearMajorana n v) * parity n := by
        simp [Matrix.mul_assoc]
    _ = -linearMajorana n (((2 : ℝ) * ⟪v,w⟫) • v - w) := by
      rw [unitMajorana_conjugate n v w hv, parity_conjugate_linearMajorana]
    _ = linearMajorana n (Gaussian.LinearAlgebra.hyperplaneReflection v w) := by
      rw [Gaussian.LinearAlgebra.hyperplaneReflection, Submodule.reflection_orthogonal_apply,
        linearMajorana_neg, Submodule.reflection_singleton_apply, hv]
      simp [two_smul, two_mul, add_smul]

theorem reflection_implemented (n : ℕ) (v : CoefficientSpace n) :
    ∃ U, Implements n (Gaussian.LinearAlgebra.hyperplaneReflection v) U := by
  by_cases hv : v=0
  · subst v
    refine ⟨1,?_⟩
    intro w
    simp [Gaussian.LinearAlgebra.hyperplaneReflection, Submodule.reflection_apply,
      Submodule.starProjection_top, two_smul]
  · let u := ‖v‖⁻¹ • v
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖u‖=1 := by
      dsimp [u]
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
    have hspan : ℝ ∙ u = ℝ ∙ v :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn)) v
    refine ⟨parityUnitary n * unitMajoranaUnitary n u hu, ?_⟩
    have h := unit_reflection_implemented n u hu
    simpa only [Gaussian.LinearAlgebra.hyperplaneReflection, hspan] using h

theorem implements_one (n : ℕ) : Implements n 1 1 := by
  intro v
  simp

theorem implements_mul (n : ℕ)
    {R S : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n}
    {U V : Matrix.unitaryGroup (Occupation n) ℂ}
    (hU : Implements n R U) (hV : Implements n S V) :
    Implements n (R*S) (U*V) := by
  intro w
  change ((U : Operator n) * (V : Operator n)) * linearMajorana n w *
    ((U : Operator n) * (V : Operator n))ᴴ = _
  rw [Matrix.conjTranspose_mul]
  calc
    ((U : Operator n) * (V : Operator n)) * linearMajorana n w *
        ((V : Operator n)ᴴ * (U : Operator n)ᴴ) =
      (U : Operator n) * ((V : Operator n) * linearMajorana n w * (V : Operator n)ᴴ) *
        (U : Operator n)ᴴ := by simp [Matrix.mul_assoc]
    _ = linearMajorana n (R (S w)) := by rw [hV, hU]
    _ = _ := rfl

theorem implements_inv (n : ℕ)
    {R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n}
    {U : Matrix.unitaryGroup (Occupation n) ℂ}
    (hU : Implements n R U) : Implements n R⁻¹ U⁻¹ := by
  intro w
  have hleft : (U : Operator n)ᴴ * (U : Operator n) = 1 := U.property.1
  change (U : Operator n)ᴴ * linearMajorana n w * ((U : Operator n)ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_conjTranspose]
  have hr : R (R⁻¹ w) = w := R.apply_symm_apply w
  nth_rw 1 [← hr]
  rw [← hU]
  calc
    (U : Operator n)ᴴ * ((U : Operator n) * linearMajorana n (R⁻¹ w) * (U : Operator n)ᴴ) *
        (U : Operator n) =
      ((U : Operator n)ᴴ * (U : Operator n)) * linearMajorana n (R⁻¹ w) *
        ((U : Operator n)ᴴ * (U : Operator n)) := by simp [Matrix.mul_assoc]
    _ = linearMajorana n (R⁻¹ w) := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

def implementedGroup (n : ℕ) : Subgroup (CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) where
  carrier := { R | ∃ U, Implements n R U }
  one_mem' := ⟨1,implements_one n⟩
  mul_mem' := by
    rintro R S ⟨U,hU⟩ ⟨V,hV⟩
    exact ⟨U*V,implements_mul n hU hV⟩
  inv_mem' := by
    rintro R ⟨U,hU⟩
    exact ⟨U⁻¹,implements_inv n hU⟩

theorem orthogonal_implemented (n : ℕ)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    ∃ U : Matrix.unitaryGroup (Occupation n) ℂ, Implements n R U := by
  have hle : Gaussian.LinearAlgebra.reflectionGroup (E := CoefficientSpace n) ≤ implementedGroup n := by
    apply (Subgroup.closure_le (implementedGroup n)).mpr
    rintro _ ⟨v,rfl⟩
    exact reflection_implemented n v
  exact hle (Gaussian.LinearAlgebra.orthogonal_mem_reflectionGroup R)

end Gaussian.Physical.Fermion
