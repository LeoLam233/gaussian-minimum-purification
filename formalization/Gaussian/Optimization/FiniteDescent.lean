import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Exact finite-total descent. This is a general theorem with explicit
hypotheses; sector-specific physical proofs of those hypotheses are mandatory.
In particular deletion is required only at actual attained minima, not at
arbitrary states or approximately minimizing sequences. -/
noncomputable section
namespace Gaussian.Optimization

/-- A genuine minimum at each finite total, deletion only at those minima,
and padding from smaller totals produce an actual global witness. -/
theorem global_attained_from_optimal_deletion
    (E : ℕ → Type*) (cost : ∀ M, E M → ℝ) (n : ℕ)
    (attain : ∀ M, n ≤ M → ∃ p : E M, ∀ x : E M, cost M p ≤ cost M x)
    (delete : ∀ M, n ≤ M → ∀ p : E (M+1),
      (∀ x : E (M+1), cost (M+1) p ≤ cost (M+1) x) →
      ∃ q : E M, cost M q ≤ cost (M+1) p)
    (pad : ∀ M, M < n → ∀ x : E M, ∃ y : E n, cost n y ≤ cost M x) :
    ∃ p : E n, ∀ M, ∀ x : E M, cost n p ≤ cost M x := by
  have lower : ∀ M, n ≤ M → ∀ x : E M, ∃ y : E n, cost n y ≤ cost M x := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => intro x; exact ⟨x,le_rfl⟩
    | succ M hM ih =>
      intro x
      obtain ⟨p,hp⟩ := attain (M+1) (by omega)
      obtain ⟨q,hq⟩ := delete M hM p hp
      obtain ⟨y,hy⟩ := ih q
      exact ⟨y,hy.trans (hq.trans (hp x))⟩
  obtain ⟨p,hp⟩ := attain n le_rfl
  refine ⟨p,?_⟩
  intro M x
  obtain ⟨y,hy⟩ : ∃ y : E n, cost n y ≤ cost M x := by
    by_cases hM : n ≤ M
    · exact lower M hM x
    · exact pad M (by omega) x
  exact (hp y).trans hy

/-- Matching the sidewise split at the capped total gives a matched witness
compared against every finite auxiliary total, not merely equal infima. -/
theorem matched_global_attained_from_optimal_deletion
    (E : ℕ → Type*) (cost : ∀ M, E M → ℝ) (n : ℕ)
    (W : Type*) (matchedCost : W → ℝ)
    (attain : ∀ M, n ≤ M → ∃ p : E M, ∀ x : E M, cost M p ≤ cost M x)
    (delete : ∀ M, n ≤ M → ∀ p : E (M+1),
      (∀ x : E (M+1), cost (M+1) p ≤ cost (M+1) x) →
      ∃ q : E M, cost M q ≤ cost (M+1) p)
    (pad : ∀ M, M < n → ∀ x : E M, ∃ y : E n, cost n y ≤ cost M x)
    (matchSplit : ∀ p : E n, ∃ w : W, matchedCost w ≤ cost n p) :
    ∃ w : W, ∀ M, ∀ x : E M, matchedCost w ≤ cost M x := by
  obtain ⟨p,hp⟩ := global_attained_from_optimal_deletion E cost n attain delete pad
  obtain ⟨w,hw⟩ := matchSplit p
  exact ⟨w,fun M x => hw.trans (hp M x)⟩

end Gaussian.Optimization
