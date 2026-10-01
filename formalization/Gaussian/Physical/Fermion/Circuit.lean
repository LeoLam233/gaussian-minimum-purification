import Gaussian.Physical.Fermion.Restriction

noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

/-- Covariance transport is a theorem about actual conjugated density matrices. -/
theorem adjacentState_covariance (n : ℕ) (i : Fin n) (ρ : Density (n+1))
    (a b : MajoranaIndex (n+1)) :
    covariance (adjacentState n i ρ) a b =
      covariance ρ (modeExchange n i a.1,a.2) (modeExchange n i b.1,b.2) := by
  unfold covariance
  rw [adjacentState_expectation, Matrix.mul_sub, Matrix.sub_mul,
    conjugate_mul _ _ _ (adjacentGate_square n i),
    conjugate_mul _ _ _ (adjacentGate_square n i),
    adjacentGate_majorana, adjacentGate_majorana]

/-- Ordered finite lists of genuine neighboring CAR moves. -/
def circuitState (n : ℕ) : List (Fin n) → Density (n+1) → Density (n+1)
  | [], ρ => ρ
  | i :: w, ρ => circuitState n w (adjacentState n i ρ)

/-- Labels of the original modes whose observables occupy each output position. -/
def circuitMode (n : ℕ) : List (Fin n) → Fin (n+1) → Fin (n+1)
  | [], j => j
  | i :: w, j => modeExchange n i (circuitMode n w j)

theorem circuitState_covariance (n : ℕ) (w : List (Fin n)) (ρ : Density (n+1))
    (a b : MajoranaIndex (n+1)) :
    covariance (circuitState n w ρ) a b =
      covariance ρ (circuitMode n w a.1,a.2) (circuitMode n w b.1,b.2) := by
  induction w generalizing ρ with
  | nil => rfl
  | cons i w ih =>
    rw [circuitState, ih, adjacentState_covariance]
    rfl

@[simp] theorem circuitState_entropy (n : ℕ) (w : List (Fin n)) (ρ : Density (n+1)) :
    Sᵥₙ (circuitState n w ρ) = Sᵥₙ ρ := by
  induction w generalizing ρ with
  | nil => rfl
  | cons i w ih => rw [circuitState, ih, entropy_adjacentState]

/-- Actual purity is invariant under every finite graded mode circuit. -/
theorem circuitState_pure_iff (n : ℕ) (w : List (Fin n)) (ρ : Density (n+1)) :
    (∃ ψ, circuitState n w ρ = MState.pure ψ) ↔ ∃ ψ, ρ = MState.pure ψ := by
  induction w generalizing ρ with
  | nil => rfl
  | cons i w ih =>
    rw [circuitState, ih, MState.pure_iff_constant_spectrum,
      MState.pure_iff_constant_spectrum]
    simp [adjacentState]

/-- Physical restriction after an arbitrary finite sequence of signed moves.
There are k+1 retained and l discarded modes; the empty retained case is separately
covered by prefixRestriction 0 l. -/
def circuitRestriction (k l : ℕ) (w : List (Fin (l+k)))
    (ρ : Density (l+(k+1))) : Density (k+1) :=
  prefixRestriction (k+1) l (circuitState (l+k) w ρ)

/-- Complete-mode covariance restriction, including noncontiguous modes reached
by a graded circuit.  The definition on the left is an actual density partial trace. -/
theorem circuitRestriction_covariance (k l : ℕ) (w : List (Fin (l+k)))
    (ρ : Density (l+(k+1))) (a b : MajoranaIndex (k+1)) :
    covariance (circuitRestriction k l w ρ) a b =
      covariance ρ
        (circuitMode (l+k) w (prefixIndex (k+1) l a.1),a.2)
        (circuitMode (l+k) w (prefixIndex (k+1) l b.1),b.2) := by
  rw [circuitRestriction, prefixRestriction_covariance, circuitState_covariance]

/-- The three-mode circuit exchanging modes1 and2 retains modes0 and2. -/
theorem noncontiguous_three_mode_covariance (ρ : Density 3) (a b : MajoranaIndex 2) :
    covariance (circuitRestriction 1 1 [1] ρ) a b =
      covariance ρ
        (Fin.cases 0 (fun _ => (2 : Fin 3)) a.1,a.2)
        (Fin.cases 0 (fun _ => (2 : Fin 3)) b.1,b.2) := by
  rw [circuitRestriction_covariance]
  have hi (j : Fin 2) :
      circuitMode 2 [1] (prefixIndex 2 1 j) = Fin.cases 0 (fun _ => (2 : Fin 3)) j := by
    fin_cases j <;> rfl
  rw [hi, hi]

end Gaussian.Physical.Fermion
