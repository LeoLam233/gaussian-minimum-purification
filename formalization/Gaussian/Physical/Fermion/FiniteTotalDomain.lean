import Gaussian.Physical.Fermion.FiniteTotal
import Gaussian.Physical.Fermion.PaddingFeasibility

noncomputable section
namespace Gaussian.Physical.Fermion

/-- A genuine finite-total feasible point consists of its sidewise cut and
an actual pure raw Wick density with the fixed physical marginal. -/
def FinitePurifier (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ) :=
  {p : Fin (M+1) × Density (M+(nA+nB)) //
    IsPureQuasifree p.2 ∧ prefixRestriction (nA+nB) M p.2=ρ}

def finitePurifierCost (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (p : FinitePurifier nA nB ρ M) : ℝ :=
  finiteTotalEntropy nA nB M p.val.1 p.val.2

theorem finitePurifier_nonempty (nA nB : ℕ) (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ)
    (M : ℕ) (hM : nA+nB≤M) : Nonempty (FinitePurifier nA nB ρ M) := by
  obtain ⟨σ,hσ,hm⟩ := exists_quasifree_purification_of_le (nA+nB) M hM ρ hρ
  exact ⟨⟨(0,σ),hσ,hm⟩⟩

/-- The actual sector-specific fixed-total attainment hypothesis required by
finite descent, with no realizability or finite-minimum assumption. -/
theorem finitePurifier_attainment (nA nB : ℕ) (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ)
    (M : ℕ) (hM : nA+nB≤M) :
    ∃ p : FinitePurifier nA nB ρ M,
      ∀ x : FinitePurifier nA nB ρ M,finitePurifierCost nA nB ρ M p≤finitePurifierCost nA nB ρ M x := by
  obtain ⟨j,σ,hσ,hm,hmin⟩ := exists_finiteTotal_minimum nA nB M ρ
    (exists_quasifree_purification_of_le (nA+nB) M hM ρ hρ)
  refine ⟨⟨(j,σ),hσ,hm⟩,?_⟩
  intro x
  exact hmin x.val.1 x.val.2 x.property.1 x.property.2

end Gaussian.Physical.Fermion
