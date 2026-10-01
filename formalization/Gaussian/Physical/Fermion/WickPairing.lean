import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.InsertIdx

noncomputable section
open scoped BigOperators
namespace Gaussian.Physical.Fermion

/-- Wick's pairing recursion, including the empty and odd words. -/
def wickValue {α : Type*} (C : α → α → ℂ) : (l : List α) → ℂ
  | [] => 1
  | a :: l => ∑ i : Fin l.length,
      (-1 : ℂ) ^ i.val * C a (l.get i) * wickValue C (l.eraseIdx i.val)
termination_by l => l.length
decreasing_by
  simp only [List.length_eraseIdx, i.isLt, ite_true, List.length_cons]
  omega

@[simp] theorem wickValue_nil {α : Type*} (C : α → α → ℂ) : wickValue C [] = 1 := by
  rw [wickValue]

@[simp] theorem wickValue_singleton {α : Type*} (C : α → α → ℂ) (a : α) :
    wickValue C [a] = 0 := by simp [wickValue]

@[simp] theorem wickValue_pair {α : Type*} (C : α → α → ℂ) (a b : α) :
    wickValue C [a,b] = C a b := by simp [wickValue]

/-- Wick pairings commute with arbitrary relabeling of their arguments. -/
theorem wickValue_map {α β : Type*} (C : β → β → ℂ) (f : α → β) (l : List α) :
    wickValue C (l.map f) = wickValue (fun a b => C (f a) (f b)) l := by
  induction l using wickValue.induct with
  | case1 => simp only [List.map_nil, wickValue_nil]
  | case2 a l ih =>
    simp only [List.map_cons, wickValue]
    apply Fintype.sum_equiv (finCongr (List.length_map (as := l) f))
    intro i
    have hi : i.val < l.length := by simpa using i.isLt
    simp only [finCongr_apply, Fin.val_cast, List.get_eq_getElem,
      List.getElem_map, List.eraseIdx_map]
    rw [ih ⟨i.val,hi⟩]

/-- Every odd Wick polynomial vanishes, regardless of its two-point kernel. -/
theorem wickValue_odd {α : Type*} (C : α → α → ℂ) (l : List α) (hl : Odd l.length) :
    wickValue C l = 0 := by
  revert hl
  induction l using wickValue.induct with
  | case1 => simp
  | case2 a l ih =>
    intro hl
    rw [wickValue]
    apply Finset.sum_eq_zero
    intro i _
    have ho : Odd (l.eraseIdx i.val).length := by
      rw [List.length_eraseIdx,if_pos i.isLt,Nat.odd_iff]
      have hr := Nat.odd_iff.mp hl
      simp only [List.length_cons] at hr
      have hi := i.isLt
      omega
    rw [ih i ho, mul_zero]

/-- Normalization, odd vanishing, and the even first-slot recurrence determine Wick moments. -/
theorem wickValue_eq_of_recursion {α : Type*} (C : α → α → ℂ) (F : List α → ℂ)
    (hNil : F [] = 1) (hOdd : ∀ l, Odd l.length → F l = 0)
    (hEven : ∀ a l, Odd l.length → F (a::l) =
      ∑ i : Fin l.length, (-1:ℂ)^i.val * C a (l.get i) * F (l.eraseIdx i.val))
    (l : List α) : F l = wickValue C l := by
  induction l using wickValue.induct with
  | case1 => simpa using hNil
  | case2 a l ih =>
    by_cases ho : Odd l.length
    · rw [hEven a l ho,wickValue]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i]
    · have hc : Odd (a::l).length := by
        rw [Nat.odd_iff] at ho ⊢
        simp only [List.length_cons]
        omega
      rw [hOdd _ hc,wickValue_odd C _ hc]

end Gaussian.Physical.Fermion
