import Gaussian.Physical.Fermion.WardSpace
import Gaussian.Physical.Fermion.WickPairing

/-! From proved first-slot Ward identities to Wick's rule for arbitrary matrix fields. -/
noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion
variable {d α : Type*} [Fintype d] [DecidableEq d]

def matrixWordMoment (D : Matrix d d ℂ) (c : α → Matrix d d ℂ) (l : List α) : ℂ :=
  (D*(l.map c).prod).trace

@[simp] theorem matrixWordMoment_nil (D : Matrix d d ℂ) (c : α → Matrix d d ℂ) :
    matrixWordMoment D c [] = D.trace := by simp [matrixWordMoment]

@[simp] theorem matrixWordMoment_pair (D : Matrix d d ℂ) (c : α → Matrix d d ℂ) (a b : α) :
    matrixWordMoment D c [a,b] = (D*(c a*c b)).trace := by simp [matrixWordMoment]

theorem matrixWordMoment_ward (D : Matrix d d ℂ) (c : α → Matrix d d ℂ) (a : α) (l : List α)
    (h : c a ∈ wordWardSpace D (l.map c)) :
    matrixWordMoment D c (a::l) = ∑ i : Fin l.length,
      (-1:ℂ)^i.val * matrixWordMoment D c [a,l.get i] *
        matrixWordMoment D c (l.eraseIdx i.val) := by
  change (D*(c a*(l.map c).prod)).trace = _
  calc
    (D*(c a*(l.map c).prod)).trace = ∑ i : Fin (l.map c).length,
      (-1:ℂ)^i.val * (D*(c a*(l.map c).get i)).trace *
        (D*((l.map c).eraseIdx i.val).prod).trace := h
    _ = _ := by
      apply Fintype.sum_equiv (finCongr (List.length_map (as := l) c))
      intro i
      simp only [finCongr_apply, Fin.val_cast, List.get_eq_getElem, List.getElem_map,
        List.eraseIdx_map, matrixWordMoment_pair, matrixWordMoment, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]

theorem matrixWordMoment_odd (D P : Matrix d d ℂ) (c : α → Matrix d d ℂ)
    (hP : P*P=1) (hD : P*D*P=D) (hc : ∀ a, P*c a*P = -c a)
    (l : List α) (hl : Odd l.length) : matrixWordMoment D c l = 0 := by
  apply trace_odd_word_zero D P hP hD (l.map c) ?_ (by simpa using hl)
  intro X hX
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hX
  exact hc a

/-- A normalized parity-invariant matrix field obeys full Wick exactly when its
proved odd-tail first-slot recurrence supplies the even moments. -/
theorem matrixWordMoment_wick (D P : Matrix d d ℂ) (c : α → Matrix d d ℂ)
    (hTrace : D.trace=1) (hP : P*P=1) (hD : P*D*P=D)
    (hc : ∀ a, P*c a*P = -c a)
    (hWard : ∀ (a : α) (l : List α), Odd l.length → c a ∈ wordWardSpace D (l.map c))
    (l : List α) :
    matrixWordMoment D c l = wickValue (fun a b => matrixWordMoment D c [a,b]) l := by
  apply wickValue_eq_of_recursion _ (matrixWordMoment D c) ?_ ?_ ?_ l
  · simpa using hTrace
  · exact matrixWordMoment_odd D P c hP hD hc
  · intro a l hl
    exact matrixWordMoment_ward D c a l (hWard a l hl)

end Gaussian.Physical.Fermion
