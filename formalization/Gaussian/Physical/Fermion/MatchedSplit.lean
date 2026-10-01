import Gaussian.Physical.Fermion.BExcessTransfer
import Gaussian.Physical.Fermion.FinitePointTransport
import Gaussian.Optimization.MatchedIteration

set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

theorem matchedWitness_of_count_equalities (nA nB a b : ℕ)
    (ha : a=nA) (hb : b=nB) (ρ : Density (nA+nB))
    (σ : Density ((a+b)+(nA+nB))) (hσ : IsSidewisePurifier nA nB a b ρ σ) :
    ∃ τ : Density ((nA+nB)+(nA+nB)),IsSidewisePurifier nA nB nA nB ρ τ ∧
      sidewiseEntropy nA nB nA nB τ=sidewiseEntropy nA nB a b σ := by
  subst a
  subst b
  exact ⟨σ,hσ,rfl⟩

theorem finitePurifier_matchSplit (nA nB : ℕ) (ρ : Density (nA+nB))
    (p : FinitePurifier nA nB ρ (nA+nB)) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ≤finitePurifierCost nA nB ρ (nA+nB) p := by
  let cost := finitePurifierCost nA nB ρ (nA+nB)
  let index := fun q : FinitePurifier nA nB ρ (nA+nB) => q.val.1.val
  have hup : ∀ x,index x<nA → ∃ y,index y=index x+1 ∧ cost y≤cost x := by
    intro x hx
    obtain ⟨a,mB,σ,hsize,hindex,hσ,hcost⟩ := finitePurifier_asSidewise nA nB ρ (nA+nB) x
    cases mB with
    | zero => dsimp [index] at hx; omega
    | succ b =>
      obtain ⟨τ,hτ,hle⟩ := exists_B_excess_transfer nA nB a b
        (by dsimp [index] at hx; omega) ρ σ hσ
      have ht : (a+1)+b=nA+nB := by omega
      let y := finitePurifierOfSidewiseAtTotal nA nB (a+1) b (nA+nB) ht ρ τ hτ
      refine ⟨y,?_,?_⟩
      · dsimp only [index,y]
        rw [finitePurifierOfSidewiseAtTotal_index,hindex]
      · change finitePurifierCost nA nB ρ (nA+nB) y≤_
        rw [finitePurifierOfSidewiseAtTotal_cost]
        exact hle.trans_eq hcost
  have hdown : ∀ x,nA < index x → ∃ y,index y+1=index x ∧ cost y≤cost x := by
    intro x hx
    obtain ⟨mA,b,σ,hsize,hindex,hσ,hcost⟩ := finitePurifier_asSidewise nA nB ρ (nA+nB) x
    cases mA with
    | zero => dsimp [index] at hx; omega
    | succ a =>
      obtain ⟨τ,hτ,hle,heq⟩ := exists_A_excess_transfer nA nB a b
        (by dsimp [index] at hx; omega) ρ σ hσ
      have ht : a+(b+1)=nA+nB := by omega
      let y := finitePurifierOfSidewiseAtTotal nA nB a (b+1) (nA+nB) ht ρ τ hτ
      refine ⟨y,?_,?_⟩
      · dsimp only [index,y]
        rw [finitePurifierOfSidewiseAtTotal_index]
        exact hindex
      · change finitePurifierCost nA nB ρ (nA+nB) y≤_
        rw [finitePurifierOfSidewiseAtTotal_cost]
        exact hle.trans_eq hcost
  obtain ⟨q,hq,hqc⟩ := Gaussian.Optimization.exists_matched_cost_le_of_unit_moves index cost nA hup hdown p
  obtain ⟨a,b,σ,hsize,hindex,hσ,hcost⟩ := finitePurifier_asSidewise nA nB ρ (nA+nB) q
  have ha : a=nA := hindex.trans hq
  have hb : b=nB := by omega
  obtain ⟨τ,hτ,hτcost⟩ := matchedWitness_of_count_equalities nA nB a b ha hb ρ σ hσ
  exact ⟨τ,hτ,hτcost.le.trans (hcost.le.trans hqc)⟩

end Gaussian.Physical.Fermion
