import Gaussian.Physical.Fermion.TerminalModeMove
import Gaussian.Physical.Fermion.ModeRelabel
import Gaussian.Physical.Fermion.SidewiseComplement

/-! Transfer the last A' complete mode to terminal B' by an actual signed CAR
mode permutation. Both the retained cut and the moved one-mode density are
identified from their genuine restrictions, not stipulated spectral data. -/
noncomputable section
namespace Gaussian.Physical.Fermion

def lastATransferEquiv (nA nB a b : ℕ) :
    Fin (((a+1)+b)+(nA+nB)) ≃ Fin ((a+(b+1))+(nA+nB)) :=
  (finCongr (by omega : ((a+1)+b)+(nA+nB)=(b+1)+((nA+nB)+a))).trans
    ((terminalModeMove ((nA+nB)+a) b).trans
      (finCongr (by omega : (b+1)+((nA+nB)+a)=(a+(b+1))+(nA+nB))))

def lastATransferState (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB))) :
    Density ((a+(b+1))+(nA+nB)) := actualModeRelabel (lastATransferEquiv nA nB a b) σ

theorem lastATransfer_inverse_fixed_val (nA nB a b : ℕ)
    (i : Fin ((a+(b+1))+(nA+nB))) (hi : i.val<(nA+nB)+a) :
    ((lastATransferEquiv nA nB a b).symm i).val=i.val := by
  change ((terminalModeMove ((nA+nB)+a) b).symm (Fin.cast (by omega) i)).val=i.val
  rw [terminalModeMove_inverse_eq_of_lt _ _ _ (by simpa only [Fin.val_cast] using hi)]
  rfl

theorem lastATransfer_inverse_last_val (nA nB a b : ℕ)
    (i : Fin ((a+(b+1))+(nA+nB))) (hi : i.val=((nA+nB)+a)+b) :
    ((lastATransferEquiv nA nB a b).symm i).val=(nA+nB)+a := by
  change ((terminalModeMove ((nA+nB)+a) b).symm (Fin.cast (by omega) i)).val=(nA+nB)+a
  exact terminalModeMove_inverse_last_val _ _ _ (by simpa only [Fin.val_cast] using hi)

theorem lastATransfer_retained_source (nA nB a b : ℕ) (i : Fin (nA+a)) :
    (lastATransferEquiv nA nB a b).symm (sidewiseSourceIndex nA nB a (b+1) i) =
      sidewiseSourceIndex nA nB (a+1) b
        (Fin.cast (by omega) (prefixIndex (nA+a) 1 i)) := by
  have hi : (sidewiseSourceIndex nA nB a (b+1) i).val<(nA+nB)+a := by
    rw [sidewiseSourceIndex_val]
    split_ifs <;> have h := i.isLt <;> omega
  apply Fin.ext
  rw [lastATransfer_inverse_fixed_val nA nB a b _ hi]
  simp only [sidewiseSourceIndex_val,Fin.val_cast,prefixIndex_val]

theorem lastATransfer_terminal_source (nA nB a b : ℕ) (i : Fin 1) :
    (lastATransferEquiv nA nB a b).symm
      (Fin.cast (by omega) (suffixIndex ((a+b)+(nA+nB)) 1 i)) =
      sidewiseSourceIndex nA nB (a+1) b
        (Fin.cast (by omega) (suffixIndex (nA+a) 1 i)) := by
  have hi0 : i.val=0 := by have h := i.isLt; omega
  have hi : (Fin.cast (by omega) (suffixIndex ((a+b)+(nA+nB)) 1 i) :
      Fin ((a+(b+1))+(nA+nB))).val=((nA+nB)+a)+b := by
    rw [Fin.val_cast,suffixIndex_val,hi0]
    omega
  apply Fin.ext
  rw [lastATransfer_inverse_last_val nA nB a b _ hi]
  simp only [sidewiseSourceIndex_val,Fin.val_cast,suffixIndex_val,hi0,add_zero]
  rw [if_neg (by omega)]
  omega

theorem lastATransfer_covariance (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (i j : MajoranaIndex ((a+(b+1))+(nA+nB))) :
    covariance (lastATransferState nA nB a b σ) i j =
      covariance σ ((lastATransferEquiv nA nB a b).symm i.1,i.2)
        ((lastATransferEquiv nA nB a b).symm j.1,j.2) :=
  actualModeRelabel_covariance _ σ i j

theorem lastATransfer_isQuasifree (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsQuasifree σ) : IsQuasifree (lastATransferState nA nB a b σ) :=
  actualModeRelabel_isQuasifree _ σ hσ

theorem lastATransfer_isPureQuasifree (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsPureQuasifree σ) : IsPureQuasifree (lastATransferState nA nB a b σ) :=
  actualModeRelabel_isPureQuasifree _ σ hσ

/-- The complete physical AB density is unchanged by the auxiliary mode transfer. -/
theorem lastATransfer_physical (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsQuasifree σ) :
    prefixRestriction (nA+nB) (a+(b+1)) (lastATransferState nA nB a b σ) =
      prefixRestriction (nA+nB) ((a+1)+b) σ := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction _ _ _ (lastATransfer_isQuasifree nA nB a b σ hσ))
    (isQuasifree_prefixRestriction _ _ σ hσ)
  intro i j
  rw [prefixRestriction_covariance,lastATransfer_covariance,prefixRestriction_covariance]
  have he (i : Fin (nA+nB)) :
      (lastATransferEquiv nA nB a b).symm (prefixIndex (nA+nB) (a+(b+1)) i) =
        prefixIndex (nA+nB) ((a+1)+b) i := by
    apply Fin.ext
    rw [lastATransfer_inverse_fixed_val nA nB a b _ (by rw [prefixIndex_val]; have h := i.isLt; omega)]
    simp only [prefixIndex_val]
  rw [he i.1,he j.1]

/-- The new actual AA' density is the old cut with its final A' mode traced out. -/
theorem lastATransfer_retained (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsQuasifree σ) :
    sidewiseRestriction nA nB a (b+1) (lastATransferState nA nB a b σ) =
      prefixRestriction (nA+a) 1 (modeCountCast (by omega) (sidewiseRestriction nA nB (a+1) b σ)) := by
  apply quasifree_eq_of_covariance _ _
    (sidewiseRestriction_isQuasifree _ _ _ _ _ (lastATransfer_isQuasifree nA nB a b σ hσ))
    (isQuasifree_prefixRestriction _ _ _ (modeCountCast_isQuasifree _ _
      (sidewiseRestriction_isQuasifree nA nB (a+1) b σ hσ)))
  intro i j
  rw [sidewiseRestriction_covariance,lastATransfer_covariance,prefixRestriction_covariance,
    modeCountCast_covariance,sidewiseRestriction_covariance]
  change covariance σ
    ((lastATransferEquiv nA nB a b).symm (sidewiseSourceIndex nA nB a (b+1) i.1),i.2)
    ((lastATransferEquiv nA nB a b).symm (sidewiseSourceIndex nA nB a (b+1) j.1),j.2) =
    covariance σ (sidewiseSourceIndex nA nB (a+1) b (Fin.cast (by omega) (prefixIndex (nA+a) 1 i.1)),i.2)
      (sidewiseSourceIndex nA nB (a+1) b (Fin.cast (by omega) (prefixIndex (nA+a) 1 j.1)),j.2)
  rw [lastATransfer_retained_source,lastATransfer_retained_source]

/-- The terminal B' marginal is exactly the selected old final A' mode. -/
theorem lastATransfer_suffix (nA nB a b : ℕ) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsQuasifree σ) :
    suffixRestriction ((a+b)+(nA+nB)) 1 (modeCountCast (by omega) (lastATransferState nA nB a b σ)) =
      suffixRestriction (nA+a) 1 (modeCountCast (by omega) (sidewiseRestriction nA nB (a+1) b σ)) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_suffixRestriction _ _ _ (modeCountCast_isQuasifree _ _
      (lastATransfer_isQuasifree nA nB a b σ hσ)))
    (isQuasifree_suffixRestriction _ _ _ (modeCountCast_isQuasifree _ _
      (sidewiseRestriction_isQuasifree nA nB (a+1) b σ hσ)))
  intro i j
  rw [suffixRestriction_covariance,modeCountCast_covariance,lastATransfer_covariance,
    suffixRestriction_covariance,modeCountCast_covariance,sidewiseRestriction_covariance]
  change covariance σ
    ((lastATransferEquiv nA nB a b).symm (Fin.cast (by omega) (suffixIndex ((a+b)+(nA+nB)) 1 i.1)),i.2)
    ((lastATransferEquiv nA nB a b).symm (Fin.cast (by omega) (suffixIndex ((a+b)+(nA+nB)) 1 j.1)),j.2) =
    covariance σ (sidewiseSourceIndex nA nB (a+1) b (Fin.cast (by omega) (suffixIndex (nA+a) 1 i.1)),i.2)
      (sidewiseSourceIndex nA nB (a+1) b (Fin.cast (by omega) (suffixIndex (nA+a) 1 j.1)),j.2)
  rw [lastATransfer_terminal_source,lastATransfer_terminal_source]

theorem lastATransfer_preserves_purifier (nA nB a b : ℕ) (ρ : Density (nA+nB))
    (σ : Density (((a+1)+b)+(nA+nB))) (hσ : IsSidewisePurifier nA nB (a+1) b ρ σ) :
    IsSidewisePurifier nA nB a (b+1) ρ (lastATransferState nA nB a b σ) :=
  ⟨lastATransfer_isPureQuasifree nA nB a b σ hσ.1,
    (lastATransfer_physical nA nB a b σ hσ.1.1).trans hσ.2⟩

end Gaussian.Physical.Fermion
