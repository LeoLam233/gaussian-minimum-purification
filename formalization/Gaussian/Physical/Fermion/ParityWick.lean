import Gaussian.Physical.Fermion.StateAction

/-! Standard parity invariance is derived from odd CAR moments using the proved
faithfulness of the actual finite matrix representation. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

theorem moment_parity_conjugation {n : ℕ} (ρ : Density n) (w : List (MajoranaIndex n)) :
    moment (ρ.uConj (parityUnitary n)) w = (-1:ℂ)^w.length * moment ρ w := by
  unfold moment
  rw [unitaryState_expectation]
  change (ρ.m*((parity n)ᴴ*wordOperator n w*parity n)).trace = _
  rw [parity_hermitian,wordOperator_parity,Matrix.mul_smul,Matrix.trace_smul]
  rfl

/-- Vanishing of all odd CAR moments forces actual parity invariance. -/
theorem parityInvariant_of_odd_moments {n : ℕ} (ρ : Density n)
    (h : ∀ w : List (MajoranaIndex n), Odd w.length → moment ρ w = 0) : ParityInvariant ρ := by
  have he : ρ.uConj (parityUnitary n) = ρ := by
    apply density_eq_of_moments
    intro w
    rw [moment_parity_conjugation]
    rcases Nat.even_or_odd w.length with hw | hw
    · rw [hw.neg_one_pow,one_mul]
    · rw [h w hw,mul_zero]
  have hm := congrArg MState.m he
  change parity n*ρ.m*(parity n)ᴴ = ρ.m at hm
  rwa [parity_hermitian] at hm

/-- The raw Wick formula itself implies the required parity domain. -/
theorem isQuasifree_of_wick {n : ℕ} (ρ : Density n)
    (h : ∀ w, moment ρ w = wickValue (fun a b => moment ρ [a,b]) w) : IsQuasifree ρ := by
  constructor
  · apply parityInvariant_of_odd_moments
    intro w hw
    rw [h,wickValue_odd _ _ hw]
  · exact h

theorem isQuasifree_iff_wick {n : ℕ} (ρ : Density n) :
    IsQuasifree ρ ↔ ∀ w, moment ρ w = wickValue (fun a b => moment ρ [a,b]) w :=
  ⟨fun h => h.2,isQuasifree_of_wick ρ⟩

end Gaussian.Physical.Fermion
