import Gaussian.Physical.Fermion.SidewiseDomain

/-! Entropy attainment over every split of a fixed finite auxiliary mode total,
for the actual pure Gaussian density domain and genuine AA' partial traces. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Compare all M+1 auxiliary sidewise allocations on one common total density space. -/
def finiteTotalEntropy (nA nB M : ℕ) (j : Fin (M+1))
    (σ : Density (M+(nA+nB))) : ℝ :=
  sidewiseEntropy nA nB j.val (M-j.val) (modeCountCast (by omega) σ)

@[fun_prop] theorem continuous_finiteTotalEntropy (nA nB M : ℕ) (j : Fin (M+1)) :
    Continuous (finiteTotalEntropy nA nB M j) :=
  (continuous_sidewiseEntropy nA nB j.val (M-j.val)).comp (continuous_modeCountCast _)

/-- Genuine fixed-total attainment, minimizing simultaneously over all M+1
complete-mode splits and all actual pure Wick purifiers.  Nonemptiness is explicit. -/
theorem exists_finiteTotal_minimum (nA nB M : ℕ) (ρ : Density (nA+nB))
    (hne : ∃ σ : Density (M+(nA+nB)),IsPureQuasifree σ ∧ prefixRestriction (nA+nB) M σ=ρ) :
    ∃ (j : Fin (M+1)) (σ : Density (M+(nA+nB))),
      IsPureQuasifree σ ∧ prefixRestriction (nA+nB) M σ=ρ ∧
      ∀ (i : Fin (M+1)) (τ : Density (M+(nA+nB))),
        IsPureQuasifree τ → prefixRestriction (nA+nB) M τ=ρ →
        finiteTotalEntropy nA nB M j σ≤finiteTotalEntropy nA nB M i τ := by
  have hm (j : Fin (M+1)) := exists_minimum_quasifreePurifiers (nA+nB) M ρ hne
    (finiteTotalEntropy nA nB M j) (continuous_finiteTotalEntropy nA nB M j)
  choose σ hσ hMarginal hmin using hm
  obtain ⟨j,hj,hjmin⟩ := Set.exists_min_image (Set.univ : Set (Fin (M+1)))
    (fun i => finiteTotalEntropy nA nB M i (σ i)) (Set.toFinite _) Set.univ_nonempty
  refine ⟨j,σ j,hσ j,hMarginal j,?_⟩
  intro i τ hτ hτm
  exact (hjmin i (Set.mem_univ i)).trans (hmin i τ hτ hτm)

/-- The fully constructed n-mode reference purifier makes the fixed physical
mode total unconditionally feasible, including zero A or B parties. -/
theorem exists_referenceTotal_minimum (nA nB : ℕ) (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ) :
    ∃ (j : Fin ((nA+nB)+1)) (σ : Density ((nA+nB)+(nA+nB))),
      IsPureQuasifree σ ∧ prefixRestriction (nA+nB) (nA+nB) σ=ρ ∧
      ∀ (i : Fin ((nA+nB)+1)) (τ : Density ((nA+nB)+(nA+nB))),
        IsPureQuasifree τ → prefixRestriction (nA+nB) (nA+nB) τ=ρ →
        finiteTotalEntropy nA nB (nA+nB) j σ≤finiteTotalEntropy nA nB (nA+nB) i τ :=
  exists_finiteTotal_minimum nA nB (nA+nB) ρ (exists_quasifree_purification (nA+nB) ρ hρ)

end Gaussian.Physical.Fermion
