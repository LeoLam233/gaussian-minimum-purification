import Gaussian.Physical.Fermion.ModeSelection
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A signed complete-mode transfer past a trailing block. The first t modes
are protected, the next mode moves to the final slot, and the remaining modes
retain their order. Physical action is supplied by the proved CAR implementation. -/
noncomputable section
namespace Gaussian.Physical.Fermion

def terminalModeLabels (t l : ℕ) : Fin t ⊕ Fin (l+1) ≃ Fin ((l+1)+t) :=
  (finSumFinEquiv (m := t) (n := l+1)).trans (finCongr (Nat.add_comm t (l+1)))

@[simp] theorem terminalModeLabels_inl_val (t l : ℕ) (i : Fin t) :
    (terminalModeLabels t l (Sum.inl i)).val=i.val := rfl

@[simp] theorem terminalModeLabels_inr_val (t l : ℕ) (i : Fin (l+1)) :
    (terminalModeLabels t l (Sum.inr i)).val=t+i.val := rfl

/-- Forward label permutation: the first tail mode moves to the end. -/
def terminalModeMove (t l : ℕ) : Equiv.Perm (Fin ((l+1)+t)) :=
  (terminalModeLabels t l).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin t)) (finRotate (l+1)).symm).trans (terminalModeLabels t l))

@[simp] theorem terminalModeMove_prefix (t l : ℕ) (i : Fin t) :
    terminalModeMove t l (terminalModeLabels t l (Sum.inl i)) = terminalModeLabels t l (Sum.inl i) := by
  simp [terminalModeMove]

@[simp] theorem terminalModeMove_inverse_prefix (t l : ℕ) (i : Fin t) :
    (terminalModeMove t l).symm (terminalModeLabels t l (Sum.inl i)) = terminalModeLabels t l (Sum.inl i) := by
  simp [terminalModeMove]

theorem terminalModeMove_eq_of_lt (t l : ℕ) (i : Fin ((l+1)+t)) (hi : i.val<t) :
    terminalModeMove t l i=i := by
  let j : Fin t := ⟨i.val,hi⟩
  have hj : terminalModeLabels t l (Sum.inl j)=i := by apply Fin.ext; rfl
  rw [← hj,terminalModeMove_prefix]

theorem terminalModeMove_inverse_eq_of_lt (t l : ℕ) (i : Fin ((l+1)+t)) (hi : i.val<t) :
    (terminalModeMove t l).symm i=i := by
  let j : Fin t := ⟨i.val,hi⟩
  have hj : terminalModeLabels t l (Sum.inl j)=i := by apply Fin.ext; rfl
  rw [← hj,terminalModeMove_inverse_prefix]

@[simp] theorem terminalModeMove_inverse_last (t l : ℕ) :
    (terminalModeMove t l).symm (terminalModeLabels t l (Sum.inr (Fin.last l))) =
      terminalModeLabels t l (Sum.inr 0) := by
  simp [terminalModeMove,finRotate_last]

@[simp] theorem terminalModeMove_first_tail (t l : ℕ) :
    terminalModeMove t l (terminalModeLabels t l (Sum.inr 0)) =
      terminalModeLabels t l (Sum.inr (Fin.last l)) := by
  exact ((terminalModeMove t l).symm_apply_eq.mp (terminalModeMove_inverse_last t l)).symm

theorem terminalModeMove_inverse_last_val (t l : ℕ) (i : Fin ((l+1)+t)) (hi : i.val=t+l) :
    ((terminalModeMove t l).symm i).val=t := by
  have he : i=terminalModeLabels t l (Sum.inr (Fin.last l)) := by
    apply Fin.ext
    simpa using hi
  rw [he,terminalModeMove_inverse_last,terminalModeLabels_inr_val]
  simp

theorem terminalModeMove_tail_apply (t l : ℕ) (i : Fin (l+1)) :
    terminalModeMove t l (terminalModeLabels t l (Sum.inr i)) =
      terminalModeLabels t l (Sum.inr ((finRotate (l+1)).symm i)) := by
  simp [terminalModeMove]

theorem terminalModeMove_val_of_gt (t l : ℕ) (i : Fin ((l+1)+t)) (hi : t < i.val) :
    (terminalModeMove t l i).val=i.val-1 := by
  let j : Fin (l+1) := ⟨i.val-t,by have := i.isLt; omega⟩
  have hj : j≠0 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val-t=0 at hv
    omega
  have he : i=terminalModeLabels t l (Sum.inr j) := by
    apply Fin.ext
    change i.val=t+(i.val-t)
    omega
  calc
    (terminalModeMove t l i).val = (terminalModeMove t l (terminalModeLabels t l (Sum.inr j))).val := by rw [← he]
    _ = t+((finRotate (l+1)).symm j).val := by rw [terminalModeMove_tail_apply,terminalModeLabels_inr_val]
    _ = t+(j.val-1) := by rw [coe_finRotate_symm_of_ne_zero hj]
    _ = i.val-1 := by dsimp [j]; omega

def terminalModeRotation (t l : ℕ) : CoefficientSpace ((l+1)+t) ≃ₗᵢ[ℝ] CoefficientSpace ((l+1)+t) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr (terminalModeMove t l) (Equiv.refl Bool))

def terminalModeUnitary (t l : ℕ) : Matrix.unitaryGroup (Occupation ((l+1)+t)) ℂ :=
  Classical.choose (orthogonal_implemented _ (terminalModeRotation t l))

theorem terminalModeUnitary_implements (t l : ℕ) :
    Implements ((l+1)+t) (terminalModeRotation t l) (terminalModeUnitary t l) :=
  Classical.choose_spec (orthogonal_implemented _ (terminalModeRotation t l))

/-- Protected complete-mode Majoranas are fixed by the genuine implemented map. -/
theorem terminalModeRotation_basis_fixed (t l : ℕ) (a : MajoranaIndex ((l+1)+t)) (ha : a.1.val<t) :
    terminalModeRotation t l (coefficientBasis ((l+1)+t) a)=coefficientBasis ((l+1)+t) a := by
  rcases a with ⟨i,b⟩
  simp [terminalModeRotation,coefficientBasis,reindexCoefficient_single,terminalModeMove_eq_of_lt t l i ha]

end Gaussian.Physical.Fermion
