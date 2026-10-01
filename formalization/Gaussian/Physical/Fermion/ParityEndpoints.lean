import Gaussian.Physical.Fermion.Thermal

noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

def vacuumOccupation : (n : ℕ) → Occupation n
  | 0 => ()
  | n+1 => (false, vacuumOccupation n)

def occupationParity : (n : ℕ) → Occupation n → ℂ
  | 0, _ => 1
  | n+1, x => (if x.1 then -1 else 1) * occupationParity n x.2

@[simp] theorem occupationParity_vacuum (n : ℕ) : occupationParity n (vacuumOccupation n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [vacuumOccupation, occupationParity, ih]

theorem parity_diagonal (n : ℕ) : parity n = Matrix.diagonal (occupationParity n) := by
  induction n with
  | zero => ext a b; cases a; cases b; simp [parity, occupationParity]
  | succ n ih =>
    rw [parity, ih, oneParity, Matrix.diagonal_kronecker_diagonal]
    rfl

theorem basisDensity_parity (n : ℕ) (x : Occupation n) :
    parity n * (MState.pure (Ket.basis x)).m =
      occupationParity n x • (MState.pure (Ket.basis x)).m := by
  rw [parity_diagonal]
  ext i j
  simp [Matrix.diagonal_mul, MState.pure_apply, Ket.basis, Ket.apply]
  by_cases hxi : x=i
  · subst i; simp
  · simp [hxi]

theorem vacuum_has_even_parity (n : ℕ) :
    HasParity (MState.pure (Ket.basis (vacuumOccupation n))) false := by
  unfold HasParity
  rw [basisDensity_parity, occupationParity_vacuum]
  rfl

theorem oneOccupied_has_odd_parity (n : ℕ) :
    HasParity (MState.pure (Ket.basis (true, vacuumOccupation n) : Ket (Occupation (n+1)))) true := by
  unfold HasParity
  rw [basisDensity_parity]
  simp [occupationParity]

theorem no_empty_odd_state (ρ : Density 0) : ¬ HasParity ρ true := by
  intro h
  have hh := congrArg Matrix.trace h
  change (1 * ρ.m).trace = ((-1 : ℂ) • ρ.m).trace at hh
  norm_num [Matrix.trace_smul, ρ.tr'] at hh

theorem oneThermal_positive_endpoint (h : (1 : ℝ) ∈ Set.Icc (-1:ℝ) 1) :
    oneThermal 1 h = MState.pure (Ket.basis false) := by
  apply MState.ext_m
  rw [oneThermal_matrix]
  ext a b
  cases a <;> cases b <;> simp [MState.pure_apply, Ket.basis, Ket.apply]

theorem oneThermal_negative_endpoint (h : (-1 : ℝ) ∈ Set.Icc (-1:ℝ) 1) :
    oneThermal (-1) h = MState.pure (Ket.basis true) := by
  apply MState.ext_m
  rw [oneThermal_matrix]
  ext a b
  cases a <;> cases b <;> simp [MState.pure_apply, Ket.basis, Ket.apply]

end Gaussian.Physical.Fermion
