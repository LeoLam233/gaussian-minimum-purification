import Gaussian.Physical.Fermion.ModeRelabel
import Gaussian.Physical.Fermion.SidewiseComplement

/-! Signed whole-party interchange. Physical AB is explicitly relabeled to BA;
all entropy equalities use the actual complementary CAR marginal. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

def physicalSwapEquiv (a b : ℕ) : Fin (a+b) ≃ Fin (b+a) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin a) (Fin b)).trans finSumFinEquiv)

def partyModeEquiv (a b c d : ℕ) : Fin ((c+d)+(a+b)) ≃ Fin ((d+c)+(b+a)) :=
  (fourModeEquiv a b c d).symm.trans
    ((Equiv.sumCongr (Equiv.sumComm (Fin a) (Fin b)) (Equiv.sumComm (Fin c) (Fin d))).trans
      (fourModeEquiv b a d c))

def physicalPartySwap (a b : ℕ) (ρ : Density (a+b)) : Density (b+a) :=
  actualModeRelabel (physicalSwapEquiv a b) ρ

def partySwapState (a b c d : ℕ) (σ : Density ((c+d)+(a+b))) : Density ((d+c)+(b+a)) :=
  actualModeRelabel (partyModeEquiv a b c d) σ

theorem physicalSwapEquiv_symm (a b : ℕ) : (physicalSwapEquiv a b).symm=physicalSwapEquiv b a := by
  rfl

theorem partyModeEquiv_symm (a b c d : ℕ) : (partyModeEquiv a b c d).symm=partyModeEquiv b a d c := by
  rfl

theorem fourModeEquiv_physical (a b c d : ℕ) (i : Fin (a+b)) :
    fourModeEquiv a b c d (Sum.inl (finSumFinEquiv.symm i))=prefixIndex (a+b) (c+d) i := by
  apply Fin.ext
  simp [fourModeEquiv,prefixIndex_val]

theorem partyModeEquiv_physical (a b c d : ℕ) (i : Fin (b+a)) :
    (partyModeEquiv a b c d).symm (prefixIndex (b+a) (d+c) i)=
      prefixIndex (a+b) (c+d) ((physicalSwapEquiv a b).symm i) := by
  rw [← fourModeEquiv_physical b a d c i]
  simp only [partyModeEquiv,Equiv.symm_trans,Equiv.trans_apply,Equiv.symm_symm,
    Equiv.symm_apply_apply]
  change (fourModeEquiv a b c d)
    (Sum.inl ((Equiv.sumComm (Fin b) (Fin a)) (finSumFinEquiv.symm i))) = _
  rw [← fourModeEquiv_physical]
  congr 2
  simp [physicalSwapEquiv]

theorem partyModeEquiv_cut (a b c d : ℕ) (i : Fin (b+d)) :
    (partyModeEquiv a b c d).symm (sidewiseSourceIndex b a d c i)=
      sidewiseComplementSourceIndex a b c d i := by
  refine Fin.addCases (fun x => ?_) (fun y => ?_) i
  · rw [sidewiseSourceIndex_eq_labels,sidewiseComplementSourceIndex_eq_labels]
    simp [partyModeEquiv,Equiv.sumSumSumComm]
  · rw [sidewiseSourceIndex_eq_labels,sidewiseComplementSourceIndex_eq_labels]
    simp [partyModeEquiv,Equiv.sumSumSumComm]

theorem partySwapState_physical (a b c d : ℕ) (σ : Density ((c+d)+(a+b)))
    (hσ : IsQuasifree σ) :
    prefixRestriction (b+a) (d+c) (partySwapState a b c d σ)=
      physicalPartySwap a b (prefixRestriction (a+b) (c+d) σ) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction _ _ _ (actualModeRelabel_isQuasifree _ _ hσ))
    (actualModeRelabel_isQuasifree _ _ (isQuasifree_prefixRestriction _ _ σ hσ))
  intro i j
  rw [prefixRestriction_covariance,actualModeRelabel_covariance,
    actualModeRelabel_covariance,prefixRestriction_covariance]
  rw [partyModeEquiv_physical,partyModeEquiv_physical]

theorem partySwapState_cut (a b c d : ℕ) (σ : Density ((c+d)+(a+b)))
    (hσ : IsQuasifree σ) :
    sidewiseRestriction b a d c (partySwapState a b c d σ)=
      sidewiseComplementRestriction a b c d σ := by
  apply quasifree_eq_of_covariance _ _
    (sidewiseRestriction_isQuasifree _ _ _ _ _ (actualModeRelabel_isQuasifree _ _ hσ))
    (sidewiseComplement_isQuasifree a b c d σ hσ)
  intro i j
  rw [sidewiseRestriction_covariance,actualModeRelabel_covariance,sidewiseComplement_covariance]
  change covariance σ ((partyModeEquiv a b c d).symm (sidewiseSourceIndex b a d c i.1),i.2)
    ((partyModeEquiv a b c d).symm (sidewiseSourceIndex b a d c j.1),j.2)=_
  rw [partyModeEquiv_cut,partyModeEquiv_cut]

theorem partySwapState_entropy (a b c d : ℕ) (σ : Density ((c+d)+(a+b)))
    (hσ : IsPureQuasifree σ) :
    sidewiseEntropy b a d c (partySwapState a b c d σ)=sidewiseEntropy a b c d σ := by
  unfold sidewiseEntropy
  rw [partySwapState_cut a b c d σ hσ.1]
  exact (sidewiseEntropy_eq_complement a b c d σ hσ).symm

theorem partySwapState_feasible (a b c d : ℕ) (ρ : Density (a+b))
    (σ : Density ((c+d)+(a+b))) (hσ : IsSidewisePurifier a b c d ρ σ) :
    IsSidewisePurifier b a d c (physicalPartySwap a b ρ) (partySwapState a b c d σ) := by
  refine ⟨actualModeRelabel_isPureQuasifree _ _ hσ.1,?_⟩
  rw [partySwapState_physical a b c d σ hσ.1.1,hσ.2]

theorem physicalPartySwap_twice (a b : ℕ) (ρ : Density (a+b)) (hρ : IsQuasifree ρ) :
    physicalPartySwap b a (physicalPartySwap a b ρ)=ρ := by
  exact actualModeRelabel_symm (physicalSwapEquiv a b) ρ hρ

theorem partySwapState_twice (a b c d : ℕ) (σ : Density ((c+d)+(a+b)))
    (hσ : IsQuasifree σ) : partySwapState b a d c (partySwapState a b c d σ)=σ := by
  exact actualModeRelabel_symm (partyModeEquiv a b c d) σ hσ

end Gaussian.Physical.Fermion
