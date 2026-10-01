import Gaussian.Physical.Fermion.Circuit
import Gaussian.Physical.Fermion.WickPairing

/-! Raw even-quasifree semantics through Wick moments of the actual density.
This definition contains no entropy, realizability, purity, or compression axioms. -/
noncomputable section
open scoped BigOperators
namespace Gaussian.Physical.Fermion

/-- The paper's parity-invariant quasifree input property, on an actual density state. -/
def IsQuasifree {n : ℕ} (ρ : Density n) : Prop :=
  ParityInvariant ρ ∧ ∀ l : List (MajoranaIndex n),
    moment ρ l = wickValue (fun a b => moment ρ [a,b]) l

/-- Actual pure admissibility; both parity components remain allowed. -/
def IsPureQuasifree {n : ℕ} (ρ : Density n) : Prop :=
  IsQuasifree ρ ∧ ∃ ψ, ρ = MState.pure ψ

/-- Wick states with the same two-point function have the same full word moments.
Turning this into density equality needs the independently proved matrix-span theorem. -/
theorem quasifree_moments_determined {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (h₂ : ∀ a b, moment ρ [a,b] = moment σ [a,b])
    (l : List (MajoranaIndex n)) : moment ρ l = moment σ l := by
  rw [hρ.2, hσ.2]
  congr 1
  funext a b
  exact h₂ a b

end Gaussian.Physical.Fermion
