import Gaussian.Physical.Fermion.AExcessTransfer
import Gaussian.Physical.Fermion.FinitePointTransport
import Gaussian.Physical.Fermion.FinitePartySwap
import Gaussian.Physical.Fermion.PureDeletion

/-! Exact optimal deletion in the actual all-split finite-total domain. The
entropy equality is obtained from an attained minimum before purity is invoked. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

theorem finitePurifier_optimal_delete_A (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (p : FinitePurifier nA nB ρ (M+1))
    (hp : ∀ x : FinitePurifier nA nB ρ (M+1),
      finitePurifierCost nA nB ρ (M+1) p≤finitePurifierCost nA nB ρ (M+1) x)
    (hexcess : nA<p.val.1.val) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q≤finitePurifierCost nA nB ρ (M+1) p := by
  obtain ⟨mA,b,σ,hsize,hindex,hσ,hcost⟩ := finitePurifier_asSidewise nA nB ρ (M+1) p
  cases mA with
  | zero => omega
  | succ a =>
    obtain ⟨τ,hτ,hle,heq⟩ := exists_A_excess_transfer_covariance nA nB a b (by omega) ρ σ hσ
    have ht : a+(b+1)=M+1 := by omega
    let p' := finitePurifierOfSidewiseAtTotal nA nB a (b+1) (M+1) ht ρ τ hτ
    have hp' : finitePurifierCost nA nB ρ (M+1) p'=sidewiseEntropy nA nB a (b+1) τ :=
      finitePurifierOfSidewiseAtTotal_cost nA nB a (b+1) (M+1) ht ρ τ hτ
    have he : sidewiseEntropy nA nB a (b+1) τ=sidewiseEntropy nA nB (a+1) b σ := by
      apply le_antisymm hle
      rw [hcost]
      exact (hp p').trans_eq hp'
    obtain ⟨δ,hδ,hδcost⟩ := exists_sidewise_pure_B_entropy_deletion nA nB a b 1 ρ τ hτ (heq he)
    have hd : a+b=M := by omega
    let q := finitePurifierOfSidewiseAtTotal nA nB a b M hd ρ δ hδ
    refine ⟨q,?_⟩
    rw [finitePurifierOfSidewiseAtTotal_cost,hδcost]
    exact hle.trans_eq hcost

/-- Every attained finite-total minimum above the physical total admits one
exact actual Gaussian mode deletion, regardless of which auxiliary side is excessive. -/
theorem finitePurifier_optimal_delete (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (hM : nA+nB≤M) (p : FinitePurifier nA nB ρ (M+1))
    (hp : ∀ x : FinitePurifier nA nB ρ (M+1),
      finitePurifierCost nA nB ρ (M+1) p≤finitePurifierCost nA nB ρ (M+1) x) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q≤finitePurifierCost nA nB ρ (M+1) p := by
  by_cases ha : nA<p.val.1.val
  · exact finitePurifier_optimal_delete_A nA nB ρ M p hp ha
  · have hρ : IsQuasifree ρ := p.property.2 ▸
      isQuasifree_prefixRestriction (nA+nB) (M+1) p.val.2 p.property.1.1
    obtain ⟨q,hqi,hqc,hqmin⟩ := finitePurifier_minimum_swap nA nB ρ (M+1) p hp
    have hqex : nB<q.val.1.val := by omega
    obtain ⟨q',hq'⟩ := finitePurifier_optimal_delete_A nB nA (physicalPartySwap nA nB ρ) M q hqmin hqex
    obtain ⟨p',hpi,hpc⟩ := exists_unswapped_finitePurifier nA nB ρ hρ M q'
    exact ⟨p',hpc.le.trans (hq'.trans_eq hqc)⟩

end Gaussian.Physical.Fermion
