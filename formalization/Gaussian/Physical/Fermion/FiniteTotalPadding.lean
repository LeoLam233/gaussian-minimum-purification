import Gaussian.Physical.Fermion.SidewisePadding
import Gaussian.Physical.Fermion.FiniteTotalDomain

noncomputable section
namespace Gaussian.Physical.Fermion

/-- Increasing only B' gives exact entropy-preserving padding between any
ordered pair of finite auxiliary totals, for every feasible actual state. -/
theorem exists_finiteTotal_padding (nA nB M L : ℕ) (hML : M≤L)
    (ρ : Density (nA+nB)) (j : Fin (M+1)) (σ : Density (M+(nA+nB)))
    (hσ : IsPureQuasifree σ) (hm : prefixRestriction (nA+nB) M σ=ρ) :
    ∃ τ : Density (L+(nA+nB)),IsPureQuasifree τ ∧ prefixRestriction (nA+nB) L τ=ρ ∧
      finiteTotalEntropy nA nB L ⟨j.val,by omega⟩ τ=finiteTotalEntropy nA nB M j σ := by
  have hold : M+(nA+nB)=(j.val+(M-j.val))+(nA+nB) := by omega
  let σ' := modeCountCast hold σ
  have hσ' : IsSidewisePurifier nA nB j.val (M-j.val) ρ σ' := by
    refine ⟨modeCountCast_isPureQuasifree hold σ hσ,?_⟩
    change prefixRestriction (nA+nB) (j.val+(M-j.val)) (modeCountCast hold σ)=ρ
    rw [prefixRestriction_cast_aux,hm]
  have hb : (M-j.val)+(L-M)=L-j.val := by omega
  have hp : ∃ τ : Density ((j.val+(L-j.val))+(nA+nB)),
      IsSidewisePurifier nA nB j.val (L-j.val) ρ τ ∧
      sidewiseEntropy nA nB j.val (L-j.val) τ=sidewiseEntropy nA nB j.val (M-j.val) σ' := by
    rw [← hb]
    exact exists_sidewise_B_entropy_padding nA nB j.val (M-j.val) (L-M) ρ σ' hσ'
  obtain ⟨τ,hτ,he⟩ := hp
  have hnew : (j.val+(L-j.val))+(nA+nB)=L+(nA+nB) := by omega
  refine ⟨modeCountCast hnew τ,modeCountCast_isPureQuasifree hnew τ hτ.1,?_,?_⟩
  · rw [prefixRestriction_cast_aux,hτ.2]
  · simpa only [finiteTotalEntropy,modeCountCast_trans,modeCountCast_rfl,σ'] using he

/-- The actual finite-total domain satisfies the entropy-preserving pure
padding hypothesis of the global finite-descent theorem. -/
theorem finitePurifier_padding (nA nB : ℕ) (ρ : Density (nA+nB)) (M L : ℕ) (hML : M≤L)
    (p : FinitePurifier nA nB ρ M) :
    ∃ q : FinitePurifier nA nB ρ L,
      finitePurifierCost nA nB ρ L q=finitePurifierCost nA nB ρ M p := by
  obtain ⟨τ,hτ,hm,he⟩ := exists_finiteTotal_padding nA nB M L hML ρ p.val.1 p.val.2 p.property.1 p.property.2
  exact ⟨⟨(⟨p.val.1.val,by omega⟩,τ),hτ,hm⟩,he⟩

end Gaussian.Physical.Fermion
