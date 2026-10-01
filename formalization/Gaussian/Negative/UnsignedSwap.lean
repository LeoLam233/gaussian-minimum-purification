import Gaussian.Physical.Fermion.GradedSwap

/-! N4 operator-level mutation control. The separate four-mode fixture tests
actual noncontiguous reduced-state purity; this file directly rejects replacing
the proved CAR exchange by unsigned spin SWAP. -/
set_option autoImplicit false
noncomputable section
open Gaussian.Physical.Fermion
open scoped Matrix Kronecker
namespace Gaussian.Negative

def unsignedSpinSwap : Matrix (Bool×Bool) (Bool×Bool) ℂ := fun x y =>
  if y=(x.2,x.1) then 1 else 0

theorem unsignedSpinSwap_square : unsignedSpinSwap*unsignedSpinSwap=1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [unsignedSpinSwap,Matrix.mul_apply,Fintype.sum_prod_type]

theorem unsignedSpinSwap_hermitian : unsignedSpinSwapᴴ=unsignedSpinSwap := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [unsignedSpinSwap,Matrix.conjTranspose_apply]

/-- Even a genuine unitary spin SWAP fails the physical CAR generator equation. -/
theorem unsignedSpinSwap_not_CAR_exchange :
    unsignedSpinSwap*(oneMajorana false ⊗ₖ (1:Matrix Bool Bool ℂ))*unsignedSpinSwap ≠
      oneParity ⊗ₖ oneMajorana false := by
  intro h
  have hh := congrArg (fun M : Matrix (Bool×Bool) (Bool×Bool) ℂ =>
    M (true,false) (true,true)) h
  norm_num [unsignedSpinSwap,oneMajorana,oneParity,Matrix.mul_apply,Fintype.sum_prod_type] at hh

end Gaussian.Negative
