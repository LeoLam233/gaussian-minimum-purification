import Gaussian.Optimization.FiniteDescent

/-! Finite exact re-splitting. These are generic iteration lemmas with explicit
one-step hypotheses, not physical purification theorems. -/
set_option autoImplicit false
namespace Gaussian.Optimization

/-- Unit moves toward a target index reach that exact index in finitely many
steps, without increasing the objective. No uniqueness or limiting claim is made. -/
theorem exists_matched_cost_le_of_unit_moves {E : Type*} (index : E → ℕ)
    (cost : E → ℝ) (target : ℕ)
    (up : ∀ x,index x<target → ∃ y,index y=index x+1 ∧ cost y≤cost x)
    (down : ∀ x,target < index x → ∃ y,index y+1=index x ∧ cost y≤cost x)
    (x : E) : ∃ y,index y=target ∧ cost y≤cost x := by
  suffices ∀ d : ℕ,∀ x : E,index x-target+(target-index x)=d →
      ∃ y,index y=target ∧ cost y≤cost x by
    exact this _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro x hx
    by_cases he : index x=target
    · exact ⟨x,he,le_rfl⟩
    by_cases hu : index x<target
    · obtain ⟨y,hy,hc⟩ := up x hu
      have hd : index y-target+(target-index y)<d := by omega
      obtain ⟨z,hz,hzc⟩ := ih _ hd y rfl
      exact ⟨z,hz,hzc.trans hc⟩
    · have hl : target < index x := by omega
      obtain ⟨y,hy,hc⟩ := down x hl
      have hd : index y-target+(target-index y)<d := by omega
      obtain ⟨z,hz,hzc⟩ := ih _ hd y rfl
      exact ⟨z,hz,hzc.trans hc⟩

/-- A previously attained minimum can therefore be attained at the exact target
split once both genuine finite one-step moves have been supplied. -/
theorem exists_matched_minimum_of_unit_moves {E : Type*} (index : E → ℕ)
    (cost : E → ℝ) (target : ℕ)
    (up : ∀ x,index x<target → ∃ y,index y=index x+1 ∧ cost y≤cost x)
    (down : ∀ x,target < index x → ∃ y,index y+1=index x ∧ cost y≤cost x)
    (x : E) (hx : ∀ z,cost x≤cost z) :
    ∃ y,index y=target ∧ cost y=cost x ∧ ∀ z,cost y≤cost z := by
  obtain ⟨y,hy,hc⟩ := exists_matched_cost_le_of_unit_moves index cost target up down x
  exact ⟨y,hy,le_antisymm hc (hx y),fun z => hc.trans (hx z)⟩

end Gaussian.Optimization
