import Gaussian.Physical.Fermion.MatrixModel

/-! The actual signed mode-exchange unitary.  In particular the doubly occupied
basis vector acquires a minus sign.  This file proves its action on Majoranas;
no unsigned spin SWAP is substituted for a CAR mode permutation. -/
noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

def gradedSwap : Matrix (Bool × Bool) (Bool × Bool) ℂ := fun x y =>
  if y = (x.2,x.1) then (if x.1 && x.2 then -1 else 1) else 0

@[simp] theorem gradedSwap_occupied : gradedSwap (true,true) (true,true) = -1 := rfl

@[simp] theorem gradedSwap_hermitian : gradedSwapᴴ = gradedSwap := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [gradedSwap, Matrix.conjTranspose_apply]

@[simp] theorem gradedSwap_square : gradedSwap * gradedSwap = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [gradedSwap, Matrix.mul_apply, Fintype.sum_prod_type]

theorem gradedSwap_first_majorana (b : Bool) :
    gradedSwap * (oneMajorana b ⊗ₖ (1 : Matrix Bool Bool ℂ)) * gradedSwap =
      oneParity ⊗ₖ oneMajorana b := by
  ext ⟨a,c⟩ ⟨d,e⟩
  cases b <;> cases a <;> cases c <;> cases d <;> cases e <;>
    simp [gradedSwap, oneMajorana, oneParity, Matrix.mul_apply, Fintype.sum_prod_type]

theorem gradedSwap_second_majorana (b : Bool) :
    gradedSwap * (oneParity ⊗ₖ oneMajorana b) * gradedSwap =
      oneMajorana b ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
  rw [← gradedSwap_first_majorana b]
  simp only [← Matrix.mul_assoc, gradedSwap_square, Matrix.one_mul]
  rw [Matrix.mul_assoc, gradedSwap_square, Matrix.mul_one]

@[simp] theorem gradedSwap_parity :
    gradedSwap * (oneParity ⊗ₖ oneParity) * gradedSwap = oneParity ⊗ₖ oneParity := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [gradedSwap, oneParity, Matrix.mul_apply, Fintype.sum_prod_type]

/-- The signed gate is an actual unitary, so it acts on all density matrices. -/
def gradedSwapUnitary : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  ⟨gradedSwap, by rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    gradedSwap_hermitian, gradedSwap_square]⟩

/-- Actual state transformation, with positivity and trace inherited from unitary conjugation. -/
def exchangeTwoModes (ρ : MState (Bool × Bool)) : MState (Bool × Bool) :=
  ρ.uConj gradedSwapUnitary

@[simp] theorem exchangeTwoModes_matrix (ρ : MState (Bool × Bool)) :
    (exchangeTwoModes ρ).m = gradedSwap * ρ.m * gradedSwap := by
  change gradedSwap * ρ.m * gradedSwapᴴ = _
  rw [gradedSwap_hermitian]

@[simp] theorem exchangeTwoModes_twice (ρ : MState (Bool × Bool)) :
    exchangeTwoModes (exchangeTwoModes ρ) = ρ := by
  apply MState.ext_m
  simp only [exchangeTwoModes_matrix, ← Matrix.mul_assoc, gradedSwap_square,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, gradedSwap_square, Matrix.mul_one]

/-- Actual density-spectrum entropy is preserved by the signed exchange. -/
@[simp] theorem entropy_exchangeTwoModes (ρ : MState (Bool × Bool)) :
    Sᵥₙ (exchangeTwoModes ρ) = Sᵥₙ ρ := by
  simp [exchangeTwoModes, Sᵥₙ]

/-- Expectation transport is proved through the actual density matrix. -/
theorem exchangeTwoModes_expectation (ρ : MState (Bool × Bool))
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    ((exchangeTwoModes ρ).m * A).trace =
      (ρ.m * (gradedSwap * A * gradedSwap)).trace := by
  rw [exchangeTwoModes_matrix]
  calc
    (gradedSwap * ρ.m * gradedSwap * A).trace =
        (gradedSwap * (ρ.m * gradedSwap * A)).trace := by simp [Matrix.mul_assoc]
    _ = ((ρ.m * gradedSwap * A) * gradedSwap).trace := Matrix.trace_mul_comm _ _
    _ = (ρ.m * (gradedSwap * A * gradedSwap)).trace := by simp [Matrix.mul_assoc]

/-- Second-mode CAR restriction: move the complete mode with the signed gate,
then take the ordinary partial trace. -/
def secondModeRestriction (ρ : MState (Bool × Bool)) : MState Bool :=
  (exchangeTwoModes ρ).traceRight

/-- The defining physical restriction theorem for both second-mode Majoranas.
The observable on the right includes its Jordan–Wigner parity string. -/
theorem secondModeRestriction_majorana (ρ : MState (Bool × Bool)) (b : Bool) :
    ((secondModeRestriction ρ).m * oneMajorana b).trace =
      (ρ.m * (oneParity ⊗ₖ oneMajorana b)).trace := by
  rw [secondModeRestriction]
  change (((exchangeTwoModes ρ).m).traceRight * oneMajorana b).trace = _
  rw [← Matrix.trace_mul_kron_one_right, exchangeTwoModes_expectation,
    gradedSwap_first_majorana]

/-- Restriction intertwines arbitrary local observables with the signed CAR embedding. -/
theorem secondModeRestriction_expectation (ρ : MState (Bool × Bool))
    (A : Matrix Bool Bool ℂ) :
    ((secondModeRestriction ρ).m * A).trace =
      (ρ.m * (gradedSwap * (A ⊗ₖ (1 : Matrix Bool Bool ℂ)) * gradedSwap)).trace := by
  change (((exchangeTwoModes ρ).m).traceRight * A).trace = _
  rw [← Matrix.trace_mul_kron_one_right, exchangeTwoModes_expectation]

end Gaussian.Physical.Fermion
