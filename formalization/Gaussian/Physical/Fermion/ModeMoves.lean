import Gaussian.Physical.Fermion.GradedSwap

noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

/-- The signed exchange of the first two modes, leaving every later mode alone. -/
def swapHead (n : ℕ) : Operator (n+2) :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc Bool Bool (Occupation n))
    (gradedSwap ⊗ₖ (1 : Operator n))

@[simp] theorem swapHead_square (n : ℕ) : swapHead n * swapHead n = 1 := by
  unfold swapHead
  rw [← map_mul, ← Matrix.mul_kronecker_mul, gradedSwap_square, Matrix.one_mul,
    Matrix.one_kronecker_one, map_one]

@[simp] theorem swapHead_hermitian (n : ℕ) : (swapHead n)ᴴ = swapHead n := by
  simp [swapHead, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

/-- Conjugation calculation for an arbitrary product observable; the state is not assumed Gaussian. -/
theorem swapHead_conjugate (n : ℕ) (A B : Matrix Bool Bool ℂ) (C : Operator n) :
    swapHead n * (A ⊗ₖ (B ⊗ₖ C)) * swapHead n =
      Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc Bool Bool (Occupation n))
        ((gradedSwap * (A ⊗ₖ B) * gradedSwap) ⊗ₖ C) := by
  rw [← Matrix.kronecker_assoc]
  change _ * Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc Bool Bool (Occupation n))
    ((A ⊗ₖ B) ⊗ₖ C) * _ = _
  unfold swapHead
  rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem swapHead_first (n : ℕ) (b : Bool) :
    swapHead n * majorana (n+2) (0,b) * swapHead n =
      majorana (n+2) ((0 : Fin (n+1)).succ,b) := by
  rw [majorana_zero, majorana_succ, majorana_zero,
    ← Matrix.one_kronecker_one (m := Bool) (n := Occupation n),
    swapHead_conjugate, gradedSwap_first_majorana]
  exact Matrix.kronecker_assoc _ _ _

@[simp] theorem swapHead_second (n : ℕ) (b : Bool) :
    swapHead n * majorana (n+2) ((0 : Fin (n+1)).succ,b) * swapHead n =
      majorana (n+2) (0,b) := by
  rw [← swapHead_first n b]
  simp only [← Matrix.mul_assoc, swapHead_square, Matrix.one_mul]
  rw [Matrix.mul_assoc, swapHead_square, Matrix.mul_one, Matrix.one_mul]

@[simp] theorem swapHead_later (n : ℕ) (i : Fin n) (b : Bool) :
    swapHead n * majorana (n+2) (i.succ.succ,b) * swapHead n =
      majorana (n+2) (i.succ.succ,b) := by
  rw [majorana_succ, majorana_succ, swapHead_conjugate, gradedSwap_parity]
  exact Matrix.kronecker_assoc _ _ _

@[simp] theorem swapHead_parity (n : ℕ) :
    swapHead n * parity (n+2) * swapHead n = parity (n+2) := by
  rw [parity, parity, swapHead_conjugate, gradedSwap_parity]
  exact Matrix.kronecker_assoc _ _ _

/-- Position k exchanges the neighboring complete modes k and k+1. -/
def adjacentGate : (n : ℕ) → Fin n → Operator (n+1)
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.cases (swapHead n)
      (fun j => (1 : Matrix Bool Bool ℂ) ⊗ₖ adjacentGate n j) i

@[simp] theorem adjacentGate_zero (n : ℕ) : adjacentGate (n+1) 0 = swapHead n := rfl
@[simp] theorem adjacentGate_succ (n : ℕ) (i : Fin n) :
    adjacentGate (n+1) i.succ = (1 : Matrix Bool Bool ℂ) ⊗ₖ adjacentGate n i := rfl

@[simp] theorem adjacentGate_square (n : ℕ) (i : Fin n) :
    adjacentGate n i * adjacentGate n i = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact swapHead_square n
    · rw [adjacentGate_succ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, ih,
        Matrix.one_kronecker_one]

@[simp] theorem adjacentGate_hermitian (n : ℕ) (i : Fin n) :
    (adjacentGate n i)ᴴ = adjacentGate n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact swapHead_hermitian n
    · simp only [adjacentGate_succ, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ih]

@[simp] theorem adjacentGate_parity (n : ℕ) (i : Fin n) :
    adjacentGate n i * parity (n+1) * adjacentGate n i = parity (n+1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact swapHead_parity n
    · rw [adjacentGate_succ, parity, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, ih]

/-- The mode-label action of the neighboring exchange, defined without any spectral data. -/
def modeExchange : (n : ℕ) → Fin n → Fin (n+1) → Fin (n+1)
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.cases
      (Fin.cases (0 : Fin (n+1)).succ
        (fun j => Fin.cases 0 (fun k => k.succ.succ) j))
      (fun i => Fin.cases 0 (fun j => (modeExchange n i j).succ)) i

@[simp] theorem modeExchange_zero_first (n : ℕ) :
    modeExchange (n+1) 0 0 = (0 : Fin (n+1)).succ := rfl
@[simp] theorem modeExchange_zero_second (n : ℕ) :
    modeExchange (n+1) 0 (0 : Fin (n+1)).succ = 0 := rfl
@[simp] theorem modeExchange_zero_later (n : ℕ) (j : Fin n) :
    modeExchange (n+1) 0 j.succ.succ = j.succ.succ := rfl
@[simp] theorem modeExchange_succ_first (n : ℕ) (i : Fin n) :
    modeExchange (n+1) i.succ 0 = 0 := rfl
@[simp] theorem modeExchange_succ_later (n : ℕ) (i : Fin n) (j : Fin (n+1)) :
    modeExchange (n+1) i.succ j.succ = (modeExchange n i j).succ := rfl

/-- Every neighboring gate implements its complete-mode permutation on both Majoranas. -/
theorem adjacentGate_majorana (n : ℕ) (i : Fin n) (j : Fin (n+1)) (b : Bool) :
    adjacentGate n i * majorana (n+1) (j,b) * adjacentGate n i =
      majorana (n+1) (modeExchange n i j,b) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact swapHead_first n b
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact swapHead_second n b
        · exact swapHead_later n j b
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [adjacentGate_succ, majorana_zero, modeExchange_succ_first,
          majorana_zero, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, adjacentGate_square]
      · rw [adjacentGate_succ, majorana_succ, modeExchange_succ_later,
          majorana_succ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul, Matrix.mul_one, ih]

@[simp] theorem modeExchange_involutive (n : ℕ) (i : Fin n) (j : Fin (n+1)) :
    modeExchange n i (modeExchange n i j) = j := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · simp only [modeExchange_succ_later, ih]

/-- Actual unitary for a neighboring exchange at any finite mode count. -/
def adjacentUnitary (n : ℕ) (i : Fin n) : Matrix.unitaryGroup (Occupation (n+1)) ℂ :=
  ⟨adjacentGate n i, by rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    adjacentGate_hermitian, adjacentGate_square]⟩

/-- Physical action on arbitrary density states, not just covariance matrices. -/
def adjacentState (n : ℕ) (i : Fin n) (ρ : Density (n+1)) : Density (n+1) :=
  ρ.uConj (adjacentUnitary n i)

@[simp] theorem adjacentState_matrix (n : ℕ) (i : Fin n) (ρ : Density (n+1)) :
    (adjacentState n i ρ).m = adjacentGate n i * ρ.m * adjacentGate n i := by
  change adjacentGate n i * ρ.m * (adjacentGate n i)ᴴ = _
  rw [adjacentGate_hermitian]

@[simp] theorem entropy_adjacentState (n : ℕ) (i : Fin n) (ρ : Density (n+1)) :
    Sᵥₙ (adjacentState n i ρ) = Sᵥₙ ρ := by simp [adjacentState, Sᵥₙ]

theorem adjacentState_expectation (n : ℕ) (i : Fin n) (ρ : Density (n+1))
    (A : Operator (n+1)) :
    ((adjacentState n i ρ).m * A).trace =
      (ρ.m * (adjacentGate n i * A * adjacentGate n i)).trace := by
  rw [adjacentState_matrix]
  calc
    (adjacentGate n i * ρ.m * adjacentGate n i * A).trace =
        (adjacentGate n i * (ρ.m * adjacentGate n i * A)).trace := by simp [Matrix.mul_assoc]
    _ = ((ρ.m * adjacentGate n i * A) * adjacentGate n i).trace := Matrix.trace_mul_comm _ _
    _ = (ρ.m * (adjacentGate n i * A * adjacentGate n i)).trace := by simp [Matrix.mul_assoc]

end Gaussian.Physical.Fermion
