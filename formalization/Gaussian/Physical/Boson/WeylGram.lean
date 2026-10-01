import Gaussian.Physical.Boson.PositiveExpectation
import Gaussian.Physical.Boson.Characteristic

/-! The actual bounded Weyl-increment Gram expression. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def incrementCombination (U V : H →L[ℂ] H) : H →L[ℂ] H :=
  (U-1)+Complex.I • (V-1)

theorem NormalDensity.incrementGram_expect (ρ : NormalDensity H)
    (U V : unitary (H →L[ℂ] H)) :
    ρ.expect (star (incrementCombination (U : H →L[ℂ] H) (V : H →L[ℂ] H))*
      incrementCombination (U : H →L[ℂ] H) (V : H →L[ℂ] H)) =
      (2-ρ.expect (U : H →L[ℂ] H)-ρ.expect (star (U : H →L[ℂ] H)))+
      (2-ρ.expect (V : H →L[ℂ] H)-ρ.expect (star (V : H →L[ℂ] H)))+
      Complex.I*(ρ.expect (star (U : H →L[ℂ] H)*(V : H →L[ℂ] H))-
        ρ.expect (star (U : H →L[ℂ] H))-ρ.expect (V : H →L[ℂ] H)+1)-
      Complex.I*(ρ.expect (star (V : H →L[ℂ] H)*(U : H →L[ℂ] H))-
        ρ.expect (star (V : H →L[ℂ] H))-ρ.expect (U : H →L[ℂ] H)+1) := by
  unfold incrementCombination
  simp only [star_add,star_sub,star_one,star_smul,Complex.star_def,Complex.conj_I,
    add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    smul_smul,Unitary.coe_star_mul_self]
  simp only [ρ.expect_add,ρ.expect_sub,ρ.expect_smul,ρ.expect_one]
  simp only [mul_neg,neg_mul,Complex.I_mul_I]
  ring_nf <;> simp [Complex.I_sq] <;> ring

theorem NormalDensity.incrementGram_nonneg (ρ : NormalDensity H)
    (U V : unitary (H →L[ℂ] H)) :
    0≤((2-ρ.expect (U : H →L[ℂ] H)-ρ.expect (star (U : H →L[ℂ] H)))+
      (2-ρ.expect (V : H →L[ℂ] H)-ρ.expect (star (V : H →L[ℂ] H)))+
      Complex.I*(ρ.expect (star (U : H →L[ℂ] H)*(V : H →L[ℂ] H))-
        ρ.expect (star (U : H →L[ℂ] H))-ρ.expect (V : H →L[ℂ] H)+1)-
      Complex.I*(ρ.expect (star (V : H →L[ℂ] H)*(U : H →L[ℂ] H))-
        ρ.expect (star (V : H →L[ℂ] H))-ρ.expect (U : H →L[ℂ] H)+1)).re := by
  rw [← ρ.incrementGram_expect U V]
  exact ρ.expect_star_mul_self_nonneg _

end Gaussian.Physical.Boson
