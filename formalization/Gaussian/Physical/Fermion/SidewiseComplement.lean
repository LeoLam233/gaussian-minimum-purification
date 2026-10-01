import Gaussian.Physical.Fermion.ModeSelection
import Gaussian.Physical.Fermion.SidewiseIndices
import Gaussian.Physical.Fermion.SuffixRestriction

/-! Actual BB' complementary CAR density and party bookkeeping for both sides
of the four-party entropy comparison. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- The BB' marginal after the same signed whole-mode rearrangement as AA'. -/
def sidewiseComplementRestriction (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) : Density (nB+mB) :=
  suffixRestriction (nA+mA) (nB+mB)
    (modeCountCast (by omega) (σ.uConj (sidewiseUnitary nA nB mA mB)))

theorem sidewiseComplement_isQuasifree (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsQuasifree σ) :
    IsQuasifree (sidewiseComplementRestriction nA nB mA mB σ) :=
  isQuasifree_suffixRestriction _ _ _ (modeCountCast_isQuasifree _ _
    (isQuasifree_unitary_of_implements _ σ hσ _ _ (sidewiseUnitary_implements nA nB mA mB)))

theorem sidewiseEntropy_eq_complement (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsPureQuasifree σ) :
    sidewiseEntropy nA nB mA mB σ = Sᵥₙ (sidewiseComplementRestriction nA nB mA mB σ) := by
  have hp : IsPureQuasifree (σ.uConj (sidewiseUnitary nA nB mA mB)) :=
    ⟨isQuasifree_unitary_of_implements _ σ hσ.1 _ _ (sidewiseUnitary_implements nA nB mA mB),
      (unitaryState_pure_iff σ _).mpr hσ.2⟩
  exact (pureQuasifree_suffix_entropy (nA+mA) (nB+mB) _
    (modeCountCast_isPureQuasifree _ _ hp)).symm

def sidewiseComplementSourceIndex (nA nB mA mB : ℕ) (i : Fin (nB+mB)) :
    Fin ((mA+mB)+(nA+nB)) :=
  (sidewiseModePermutation nA nB mA mB).symm
    (Fin.cast (by omega) (suffixIndex (nA+mA) (nB+mB) i))

theorem sidewiseComplementSourceIndex_eq_labels (nA nB mA mB : ℕ) (i : Fin (nB+mB)) :
    sidewiseComplementSourceIndex nA nB mA mB i =
      fourModeEquiv nA nB mA mB
        ((Equiv.sumSumSumComm (Fin nA) (Fin nB) (Fin mA) (Fin mB)).symm
          (Sum.inr (finSumFinEquiv.symm i))) := by
  apply (sidewiseModePermutation nA nB mA mB).injective
  simp only [sidewiseComplementSourceIndex,Equiv.apply_symm_apply,sidewiseModePermutation,
    Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  apply Fin.ext
  simp [fourModeEquiv,suffixIndex_val]
  omega

theorem sidewiseComplementSourceIndex_val (nA nB mA mB : ℕ) (i : Fin (nB+mB)) :
    (sidewiseComplementSourceIndex nA nB mA mB i).val =
      if i.val<nB then nA+i.val else nA+mA+i.val := by
  refine Fin.addCases (fun b => ?_) (fun d => ?_) i
  · rw [sidewiseComplementSourceIndex_eq_labels]
    simp [fourModeEquiv,Equiv.sumSumSumComm,b.isLt]
  · rw [sidewiseComplementSourceIndex_eq_labels]
    have hd : ¬nB+d.val<nB := by omega
    simp [fourModeEquiv,Equiv.sumSumSumComm,hd]
    omega

theorem sidewiseComplement_covariance (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (a b : MajoranaIndex (nB+mB)) :
    covariance (sidewiseComplementRestriction nA nB mA mB σ) a b =
      covariance σ (sidewiseComplementSourceIndex nA nB mA mB a.1,a.2)
        (sidewiseComplementSourceIndex nA nB mA mB b.1,b.2) := by
  unfold sidewiseComplementRestriction sidewiseComplementSourceIndex
  rw [suffixRestriction_covariance,modeCountCast_covariance]
  exact permutationAction_covariance _ _ _ (sidewiseUnitary_implements nA nB mA mB) σ _ _

/-- The A labels inside the actual AA' cut have exactly the original A density. -/
theorem sidewiseRestriction_physical_A (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsQuasifree σ) :
    prefixRestriction nA mA (modeCountCast (Nat.add_comm nA mA) (sidewiseRestriction nA nB mA mB σ)) =
      prefixRestriction nA nB (modeCountCast (Nat.add_comm nA nB)
        (prefixRestriction (nA+nB) (mA+mB) σ)) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction nA mA _ (modeCountCast_isQuasifree _ _
      (sidewiseRestriction_isQuasifree nA nB mA mB σ hσ)))
    (isQuasifree_prefixRestriction nA nB _ (modeCountCast_isQuasifree _ _
      (isQuasifree_prefixRestriction (nA+nB) (mA+mB) σ hσ)))
  intro a b
  rw [prefixRestriction_covariance,modeCountCast_covariance,sidewiseRestriction_covariance,
    prefixRestriction_covariance,modeCountCast_covariance,prefixRestriction_covariance]
  have hi (i : Fin nA) :
      sidewiseSourceIndex nA nB mA mB (Fin.cast (Nat.add_comm nA mA).symm (prefixIndex nA mA i)) =
        prefixIndex (nA+nB) (mA+mB) (Fin.cast (Nat.add_comm nA nB).symm (prefixIndex nA nB i)) := by
    apply Fin.ext
    simp only [sidewiseSourceIndex_val,prefixIndex_val,Fin.val_cast,if_pos i.isLt]
  change covariance σ
    (sidewiseSourceIndex nA nB mA mB (Fin.cast (Nat.add_comm nA mA).symm (prefixIndex nA mA a.1)),a.2)
    (sidewiseSourceIndex nA nB mA mB (Fin.cast (Nat.add_comm nA mA).symm (prefixIndex nA mA b.1)),b.2) = _
  rw [hi a.1,hi b.1]

/-- The B labels inside the actual BB' complement have the original CAR B density. -/
theorem sidewiseComplement_physical_B (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsQuasifree σ) :
    prefixRestriction nB mB (modeCountCast (Nat.add_comm nB mB)
      (sidewiseComplementRestriction nA nB mA mB σ)) =
      suffixRestriction nA nB (modeCountCast (Nat.add_comm nA nB)
        (prefixRestriction (nA+nB) (mA+mB) σ)) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction nB mB _ (modeCountCast_isQuasifree _ _
      (sidewiseComplement_isQuasifree nA nB mA mB σ hσ)))
    (isQuasifree_suffixRestriction nA nB _ (modeCountCast_isQuasifree _ _
      (isQuasifree_prefixRestriction (nA+nB) (mA+mB) σ hσ)))
  intro a b
  rw [prefixRestriction_covariance,modeCountCast_covariance,sidewiseComplement_covariance,
    suffixRestriction_covariance,modeCountCast_covariance,prefixRestriction_covariance]
  have hi (i : Fin nB) :
      sidewiseComplementSourceIndex nA nB mA mB (Fin.cast (Nat.add_comm nB mB).symm (prefixIndex nB mB i)) =
        prefixIndex (nA+nB) (mA+mB) (Fin.cast (Nat.add_comm nA nB).symm (suffixIndex nA nB i)) := by
    apply Fin.ext
    simp only [sidewiseComplementSourceIndex_val,prefixIndex_val,Fin.val_cast,if_pos i.isLt,suffixIndex_val]
  rw [hi a.1,hi b.1]

end Gaussian.Physical.Fermion
