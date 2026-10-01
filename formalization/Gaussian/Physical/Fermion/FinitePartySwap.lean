import Gaussian.Physical.Fermion.PartySwap
import Gaussian.Physical.Fermion.FiniteTotalDomain

set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Signed party interchange preserves every actual finite-total feasible cost. -/
theorem exists_swapped_finitePurifier (a b : ℕ) (ρ : Density (a+b)) (M : ℕ)
    (p : FinitePurifier a b ρ M) :
    ∃ q : FinitePurifier b a (physicalPartySwap a b ρ) M,
      q.val.1.val=M-p.val.1.val ∧
      finitePurifierCost b a (physicalPartySwap a b ρ) M q=finitePurifierCost a b ρ M p := by
  let j := p.val.1.val
  have hj : j≤M := by have h:=p.val.1.isLt; dsimp [j]; omega
  let h : M+(a+b)=(j+(M-j))+(a+b) := by omega
  let σ := modeCountCast h p.val.2
  have hσ : IsSidewisePurifier a b j (M-j) ρ σ := by
    refine ⟨modeCountCast_isPureQuasifree h p.val.2 p.property.1,?_⟩
    rw [prefixRestriction_cast_aux,p.property.2]
  let τ := partySwapState a b j (M-j) σ
  have hτ := partySwapState_feasible a b j (M-j) ρ σ hσ
  let hs : ((M-j)+j)+(b+a)=M+(b+a) := by omega
  let q : FinitePurifier b a (physicalPartySwap a b ρ) M :=
    ⟨(⟨M-j,by omega⟩,modeCountCast hs τ),
      modeCountCast_isPureQuasifree hs τ hτ.1,
      by rw [prefixRestriction_cast_aux,hτ.2]⟩
  refine ⟨q,rfl,?_⟩
  have he : finitePurifierCost b a (physicalPartySwap a b ρ) M q =
      sidewiseEntropy b a (M-j) j τ := by
    change sidewiseEntropy b a (M-j) (M-(M-j))
      (modeCountCast _ (modeCountCast hs τ))=_
    rw [modeCountCast_trans]
    exact sidewiseEntropy_cast_B_eq b a (M-j) (by omega) _ rfl τ
  rw [he]
  exact partySwapState_entropy a b j (M-j) σ hσ.1

/-- Swapping an actual fixed-total minimum gives a minimum of the swapped
physical problem. The inverse recovery uses the raw Wick covariance uniqueness. -/
theorem finitePurifier_minimum_swap (a b : ℕ) (ρ : Density (a+b)) (M : ℕ)
    (p : FinitePurifier a b ρ M)
    (hp : ∀ x : FinitePurifier a b ρ M,
      finitePurifierCost a b ρ M p≤finitePurifierCost a b ρ M x) :
    ∃ q : FinitePurifier b a (physicalPartySwap a b ρ) M,
      q.val.1.val=M-p.val.1.val ∧
      finitePurifierCost b a (physicalPartySwap a b ρ) M q=finitePurifierCost a b ρ M p ∧
      ∀ x : FinitePurifier b a (physicalPartySwap a b ρ) M,
        finitePurifierCost b a (physicalPartySwap a b ρ) M q≤
          finitePurifierCost b a (physicalPartySwap a b ρ) M x := by
  have hρ : IsQuasifree ρ := p.property.2 ▸
    isQuasifree_prefixRestriction (a+b) M p.val.2 p.property.1.1
  obtain ⟨q,hj,hq⟩ := exists_swapped_finitePurifier a b ρ M p
  refine ⟨q,hj,hq,?_⟩
  intro x
  have hh := exists_swapped_finitePurifier b a (physicalPartySwap a b ρ) M x
  rw [physicalPartySwap_twice a b ρ hρ] at hh
  obtain ⟨y,hyj,hy⟩ := hh
  rw [hq,← hy]
  exact hp y

/-- Any feasible cost in the swapped problem is recovered in the original
problem, with the same finite total and exactly the same entropy. -/
theorem exists_unswapped_finitePurifier (a b : ℕ) (ρ : Density (a+b))
    (hρ : IsQuasifree ρ) (M : ℕ)
    (q : FinitePurifier b a (physicalPartySwap a b ρ) M) :
    ∃ p : FinitePurifier a b ρ M,
      p.val.1.val=M-q.val.1.val ∧
      finitePurifierCost a b ρ M p=finitePurifierCost b a (physicalPartySwap a b ρ) M q := by
  have hh := exists_swapped_finitePurifier b a (physicalPartySwap a b ρ) M q
  rwa [physicalPartySwap_twice a b ρ hρ] at hh

end Gaussian.Physical.Fermion
