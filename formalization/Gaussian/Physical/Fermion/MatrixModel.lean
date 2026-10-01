import QuantumInfo.Entropy.VonNeumann
import Mathlib.Data.Fin.Tuple.Basic

/-! An explicit finite occupation representation.  The parity string is part of
all later-mode generators; ordinary unsigned tensor relabelling is not used as a
fermionic mode permutation.  No Gaussian-state correspondence is assumed here. -/
noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

/-- Recursive occupation basis, with exactly one vector when there are no modes. -/
@[reducible] def Occupation : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Occupation n

instance occupationFintype (n : ℕ) : Fintype (Occupation n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd Bool (Occupation n) inferInstance ih

instance occupationDecidableEq (n : ℕ) : DecidableEq (Occupation n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact @instDecidableEqProd Bool (Occupation n) inferInstance ih

instance occupationNonempty (n : ℕ) : Nonempty (Occupation n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => exact ⟨false, Classical.choice ih⟩

abbrev Operator (n : ℕ) := Matrix (Occupation n) (Occupation n) ℂ
abbrev Density (n : ℕ) := MState (Occupation n)

/-- Two self-adjoint Majoranas for a single complete mode. -/
def oneMajorana (b : Bool) : Matrix Bool Bool ℂ := fun i j =>
  if i = j then 0 else if b then (if i then Complex.I else -Complex.I) else 1

/-- One-mode parity: empty occupation is even and occupied is odd. -/
def oneParity : Matrix Bool Bool ℂ := Matrix.diagonal fun b => if b then -1 else 1

@[simp] theorem oneMajorana_hermitian (b : Bool) : (oneMajorana b)ᴴ = oneMajorana b := by
  ext i j
  cases b <;> cases i <;> cases j <;> simp [oneMajorana, Matrix.conjTranspose_apply]

@[simp] theorem oneParity_hermitian : oneParityᴴ = oneParity := by
  ext i j
  cases i <;> cases j <;> simp [oneParity, Matrix.conjTranspose_apply, Matrix.diagonal_apply]

@[simp] theorem oneMajorana_square (b : Bool) : oneMajorana b * oneMajorana b = 1 := by
  ext i j
  cases b <;> cases i <;> cases j <;>
    simp [oneMajorana, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply]

@[simp] theorem oneParity_square : oneParity * oneParity = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [oneParity, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Matrix.one_apply]

theorem oneMajorana_anticommute (b c : Bool) (h : b ≠ c) :
    oneMajorana b * oneMajorana c = -(oneMajorana c * oneMajorana b) := by
  ext i j
  cases b <;> cases c <;> cases i <;> cases j <;>
    simp_all [oneMajorana, Matrix.mul_apply, Fintype.sum_bool, Matrix.neg_apply]

theorem oneMajorana_parity (b : Bool) :
    oneMajorana b * oneParity = -(oneParity * oneMajorana b) := by
  ext i j
  cases b <;> cases i <;> cases j <;>
    simp [oneMajorana, oneParity, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.diagonal_apply, Matrix.neg_apply]

/-- Total parity, including the empty even sector. -/
def parity : (n : ℕ) → Operator n
  | 0 => 1
  | n + 1 => oneParity ⊗ₖ parity n

/-- Explicit Jordan–Wigner Majoranas, with a parity string for every earlier mode. -/
def majorana : (n : ℕ) → Fin n × Bool → Operator n
  | 0, a => Fin.elim0 a.1
  | n + 1, (a,b) => Fin.cases (oneMajorana b ⊗ₖ (1 : Operator n))
      (fun i => oneParity ⊗ₖ majorana n (i,b)) a

@[simp] theorem majorana_zero (n : ℕ) (b : Bool) :
    majorana (n+1) (0,b) = oneMajorana b ⊗ₖ (1 : Operator n) := rfl

@[simp] theorem majorana_succ (n : ℕ) (i : Fin n) (b : Bool) :
    majorana (n+1) (i.succ,b) = oneParity ⊗ₖ majorana n (i,b) := rfl

@[simp] theorem parity_square (n : ℕ) : parity n * parity n = 1 := by
  induction n with
  | zero => simp [parity]
  | succ n ih =>
    rw [parity, ← Matrix.mul_kronecker_mul, oneParity_square, ih,
      Matrix.one_kronecker_one]

@[simp] theorem parity_hermitian (n : ℕ) : (parity n)ᴴ = parity n := by
  induction n with
  | zero => simp [parity]
  | succ n ih => simp only [parity, Matrix.conjTranspose_kronecker,
      oneParity_hermitian, ih]

@[simp] theorem majorana_square (n : ℕ) (a : Fin n × Bool) :
    majorana n a * majorana n a = 1 := by
  induction n with
  | zero => exact Fin.elim0 a.1
  | succ n ih =>
    rcases a with ⟨i,b⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [majorana_zero, ← Matrix.mul_kronecker_mul, oneMajorana_square,
        Matrix.one_mul, Matrix.one_kronecker_one]
    · rw [majorana_succ, ← Matrix.mul_kronecker_mul, oneParity_square, ih,
        Matrix.one_kronecker_one]

@[simp] theorem majorana_hermitian (n : ℕ) (a : Fin n × Bool) :
    (majorana n a)ᴴ = majorana n a := by
  induction n with
  | zero => exact Fin.elim0 a.1
  | succ n ih =>
    rcases a with ⟨i,b⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [majorana_zero, Matrix.conjTranspose_kronecker,
        oneMajorana_hermitian, Matrix.conjTranspose_one]
    · simp only [majorana_succ, Matrix.conjTranspose_kronecker,
        oneParity_hermitian, ih]

theorem neg_kronecker_left {a b : Type*} (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by ext i j; simp

theorem neg_kronecker_right {a b : Type*} (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by ext i j; simp

/-- Distinct Majoranas anticommute, including generators on distinct modes. -/
theorem majorana_anticommute (n : ℕ) (a c : Fin n × Bool) (h : a ≠ c) :
    majorana n a * majorana n c = -(majorana n c * majorana n a) := by
  induction n with
  | zero => exact Fin.elim0 a.1
  | succ n ih =>
    rcases a with ⟨i,b⟩
    rcases c with ⟨j,d⟩
    revert h
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      have hbd : b ≠ d := fun hbd => h (by simp [hbd])
      rw [majorana_zero, majorana_zero, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneMajorana_anticommute b d hbd,
        neg_kronecker_left]
    · intro _
      rw [majorana_zero, majorana_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneMajorana_parity, Matrix.one_mul,
        Matrix.mul_one, neg_kronecker_left]
    · intro _
      rw [majorana_succ, majorana_zero, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneMajorana_parity, Matrix.one_mul,
        Matrix.mul_one, neg_kronecker_left, neg_neg]
    · intro h
      have hic : (i,b) ≠ (j,d) := fun hij => h (by cases hij; rfl)
      rw [majorana_succ, majorana_succ, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneParity_square, ih (i,b) (j,d) hic,
        neg_kronecker_right]

/-- The full CAR relation is derived from the explicit signed matrices. -/
theorem majorana_car (n : ℕ) (a c : Fin n × Bool) :
    majorana n a * majorana n c + majorana n c * majorana n a =
      if a = c then (2 : ℂ) • (1 : Operator n) else 0 := by
  by_cases h : a = c
  · subst c
    simp [two_smul]
  · rw [if_neg h, majorana_anticommute n a c h, neg_add_cancel]

/-- Every Majorana is odd for the actual total-parity matrix. -/
theorem majorana_parity (n : ℕ) (a : Fin n × Bool) :
    majorana n a * parity n = -(parity n * majorana n a) := by
  induction n with
  | zero => exact Fin.elim0 a.1
  | succ n ih =>
    rcases a with ⟨i,b⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [majorana_zero, parity, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneMajorana_parity, Matrix.one_mul,
        Matrix.mul_one, neg_kronecker_left]
    · rw [majorana_succ, parity, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, oneParity_square, ih, neg_kronecker_right]

/-- A direct identification with the usual bit-string occupation basis. -/
def occupationEquiv : (n : ℕ) → Occupation n ≃ (Fin n → Bool)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    { toFun := fun x => Fin.cons x.1 (occupationEquiv n x.2)
      invFun := fun x => (x 0, (occupationEquiv n).symm (Fin.tail x))
      left_inv := fun x => by simp
      right_inv := fun x => by simp }

/-- There is no finite-mode occupation-number truncation: dimension is exactly 2^n. -/
theorem occupation_card (n : ℕ) : Fintype.card (Occupation n) = 2 ^ n := by
  rw [Fintype.card_congr (occupationEquiv n)]
  simp

/-- Parity invariance is a raw property of an actual density matrix. -/
def ParityInvariant {n : ℕ} (ρ : Density n) : Prop :=
  parity n * ρ.m * parity n = ρ.m

/-- Definite total parity, permitting either sign in the primary optimization. -/
def HasParity {n : ℕ} (ρ : Density n) (odd : Bool) : Prop :=
  parity n * ρ.m = (if odd then (-1 : ℂ) else 1) • ρ.m

theorem hasParity_parityInvariant {n : ℕ} (ρ : Density n) (odd : Bool)
    (h : HasParity ρ odd) : ParityInvariant ρ := by
  unfold HasParity at h
  have hr : ρ.m * parity n = (if odd then (-1 : ℂ) else 1) • ρ.m := by
    have hh := congrArg Matrix.conjTranspose h
    have hρ : ρ.mᴴ = ρ.m := ρ.Hermitian
    cases odd <;> simpa only [Matrix.conjTranspose_mul, parity_hermitian, hρ,
      Matrix.conjTranspose_smul, Bool.false_eq_true, if_false, if_true,
      star_neg, star_one] using hh
  unfold ParityInvariant
  rw [h, Matrix.smul_mul, hr, smul_smul]
  cases odd <;> simp

end Gaussian.Physical.Fermion
