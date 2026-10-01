import Gaussian.Physical.Fermion.Thermal
import Gaussian.Physical.Fermion.LinearMajorana

/-! Endpoint-safe thermal pull-through identities, including vanishing weights. -/
noncomputable section
open scoped Matrix Kronecker BigOperators
namespace Gaussian.Physical.Fermion

def oneAnnihilation : Matrix Bool Bool ℂ := Matrix.single false true 1

def annihilation : (n : ℕ) → Fin n → Operator n
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.cases (oneAnnihilation ⊗ₖ (1 : Operator n))
      (fun j => oneParity ⊗ₖ annihilation n j) i

def creation (n : ℕ) (i : Fin n) : Operator n := (annihilation n i)ᴴ

@[simp] theorem annihilation_zero (n : ℕ) :
    annihilation (n+1) 0 = oneAnnihilation ⊗ₖ (1 : Operator n) := rfl
@[simp] theorem annihilation_succ (n : ℕ) (i : Fin n) :
    annihilation (n+1) i.succ = oneParity ⊗ₖ annihilation n i := rfl

theorem oneAnnihilation_majorana :
    oneAnnihilation = (1/2 : ℂ) • (oneMajorana false + Complex.I • oneMajorana true) := by
  ext a b
  cases a <;> cases b <;> norm_num [oneAnnihilation, oneMajorana, Matrix.single_apply]

theorem annihilation_majorana (n : ℕ) (i : Fin n) :
    annihilation n i = (1/2 : ℂ) •
      (majorana n (i,false) + Complex.I • majorana n (i,true)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [annihilation_zero, oneAnnihilation_majorana, Matrix.smul_kronecker,
        Matrix.add_kronecker, Matrix.smul_kronecker, majorana_zero, majorana_zero]
    · rw [annihilation_succ, ih, Matrix.kronecker_smul, Matrix.kronecker_add,
        Matrix.kronecker_smul, majorana_succ, majorana_succ]

theorem creation_majorana (n : ℕ) (i : Fin n) :
    creation n i = (1/2 : ℂ) •
      (majorana n (i,false) - Complex.I • majorana n (i,true)) := by
  simp [creation, annihilation_majorana, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, sub_eq_add_neg]

def emptyWeight (t : ℝ) : ℂ := ((1+t)/2 : ℝ)
def occupiedWeight (t : ℝ) : ℂ := ((1-t)/2 : ℝ)

@[simp] theorem thermal_weights_sum (t : ℝ) : emptyWeight t + occupiedWeight t = 1 := by
  simp only [emptyWeight, occupiedWeight, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem oneThermal_annihilation_left (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (oneThermal t ht).m * oneAnnihilation = emptyWeight t • oneAnnihilation := by
  rw [oneThermal_matrix]
  ext a b
  cases a <;> cases b <;> simp [oneAnnihilation, Matrix.mul_apply, emptyWeight]

theorem oneThermal_annihilation_right (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    oneAnnihilation * (oneThermal t ht).m = occupiedWeight t • oneAnnihilation := by
  rw [oneThermal_matrix]
  ext a b
  cases a <;> cases b <;> simp [oneAnnihilation, Matrix.mul_apply, occupiedWeight]

theorem oneThermal_commutes_parity (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (oneThermal t ht).m * oneParity = oneParity * (oneThermal t ht).m := by
  rw [oneThermal_matrix, oneParity, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  exact mul_comm _ _

theorem thermal_annihilation_balance (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n) :
    occupiedWeight (t i) • ((thermal n t ht).m * annihilation n i) =
      emptyWeight (t i) • (annihilation n i * (thermal n t ht).m) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change occupiedWeight (t 0) •
        (((oneThermal (t 0) (ht 0)).m ⊗ₖ (thermal n (fun j => t j.succ) _).m) *
          (oneAnnihilation ⊗ₖ 1)) =
        emptyWeight (t 0) • ((oneAnnihilation ⊗ₖ 1) *
          ((oneThermal (t 0) (ht 0)).m ⊗ₖ (thermal n (fun j => t j.succ) _).m))
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        oneThermal_annihilation_left, oneThermal_annihilation_right,
        Matrix.mul_one, Matrix.one_mul, Matrix.smul_kronecker, Matrix.smul_kronecker,
        smul_smul, smul_smul, mul_comm]
    · change occupiedWeight (t i.succ) •
        (((oneThermal (t 0) (ht 0)).m ⊗ₖ (thermal n (fun j => t j.succ) _).m) *
          (oneParity ⊗ₖ annihilation n i)) =
        emptyWeight (t i.succ) • ((oneParity ⊗ₖ annihilation n i) *
          ((oneThermal (t 0) (ht 0)).m ⊗ₖ (thermal n (fun j => t j.succ) _).m))
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        oneThermal_commutes_parity, ← Matrix.kronecker_smul, ← Matrix.kronecker_smul]
      congr 1
      exact ih (fun j => t j.succ) (fun j => ht j.succ) i

theorem thermal_creation_balance (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n) :
    emptyWeight (t i) • ((thermal n t ht).m * creation n i) =
      occupiedWeight (t i) • (creation n i * (thermal n t ht).m) := by
  have h := congrArg Matrix.conjTranspose (thermal_annihilation_balance n t ht i)
  have hρ : (thermal n t ht).mᴴ = (thermal n t ht).m := (thermal n t ht).Hermitian
  simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hρ, creation,
    emptyWeight, occupiedWeight, Complex.star_def, Complex.conj_ofReal] using h.symm

end Gaussian.Physical.Fermion
