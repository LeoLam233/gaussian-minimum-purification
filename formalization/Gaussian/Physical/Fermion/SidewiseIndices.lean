import Gaussian.Physical.Fermion.SidewiseDomain

noncomputable section
namespace Gaussian.Physical.Fermion

def sidewiseSourceIndex (nA nB mA mB : ℕ) (i : Fin (nA+mA)) :
    Fin ((mA+mB)+(nA+nB)) :=
  (sidewiseModePermutation nA nB mA mB).symm
    (Fin.cast (by omega) (prefixIndex (nA+mA) (nB+mB) i))

theorem sidewiseSourceIndex_eq_labels (nA nB mA mB : ℕ) (i : Fin (nA+mA)) :
    sidewiseSourceIndex nA nB mA mB i =
      fourModeEquiv nA nB mA mB
        ((Equiv.sumSumSumComm (Fin nA) (Fin nB) (Fin mA) (Fin mB)).symm
          (Sum.inl (finSumFinEquiv.symm i))) := by
  apply (sidewiseModePermutation nA nB mA mB).injective
  simp only [sidewiseSourceIndex,Equiv.apply_symm_apply,sidewiseModePermutation,
    Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  apply Fin.ext
  simp [fourModeEquiv]

/-- The AA' source labels depend on A,B,A' counts but not on the number of B' modes. -/
theorem sidewiseSourceIndex_val (nA nB mA mB : ℕ) (i : Fin (nA+mA)) :
    (sidewiseSourceIndex nA nB mA mB i).val = if i.val<nA then i.val else i.val+nB := by
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · rw [sidewiseSourceIndex_eq_labels]
    simp [fourModeEquiv,Equiv.sumSumSumComm,a.isLt]
  · rw [sidewiseSourceIndex_eq_labels]
    have hc : ¬nA+c.val<nA := by omega
    simp [fourModeEquiv,Equiv.sumSumSumComm,hc]
    omega

/-- Appending modes to B' leaves every old retained AA' label unchanged. -/
theorem sidewiseSourceIndex_padding (nA nB mA mB extra : ℕ)
    (i : Fin (nA+mA))
    (h : extra+((mA+mB)+(nA+nB))=(mA+(mB+extra))+(nA+nB)) :
    Fin.cast h.symm (sidewiseSourceIndex nA nB mA (mB+extra) i) =
      prefixIndex ((mA+mB)+(nA+nB)) extra (sidewiseSourceIndex nA nB mA mB i) := by
  apply Fin.ext
  simp only [Fin.val_cast,prefixIndex_val,sidewiseSourceIndex_val]

end Gaussian.Physical.Fermion
