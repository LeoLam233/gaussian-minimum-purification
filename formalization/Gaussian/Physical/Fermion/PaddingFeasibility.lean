import Gaussian.Physical.Fermion.PurePadding
import Gaussian.Physical.Fermion.CutEntropy

noncomputable section
namespace Gaussian.Physical.Fermion

theorem modeCountCast_isQuasifree {n m : ℕ} (h : n=m) (ρ : Density n) (hρ : IsQuasifree ρ) :
    IsQuasifree (modeCountCast h ρ) := by subst m; exact hρ

theorem modeCountCast_isPureQuasifree {n m : ℕ} (h : n=m) (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    IsPureQuasifree (modeCountCast h ρ) := by subst m; exact hρ

theorem modeCountCast_covariance {n m : ℕ} (h : n=m) (ρ : Density n) (a b : MajoranaIndex m) :
    covariance (modeCountCast h ρ) a b =
      covariance ρ (Fin.cast h.symm a.1,a.2) (Fin.cast h.symm b.1,b.2) := by
  subst m
  rfl

/-- Any feasible finite pure Gaussian purification can be extended to any
larger auxiliary mode count while preserving the original actual density. -/
theorem exists_purifier_of_auxiliary_le (k l L : ℕ) (hsize : l≤L) (ρ : Density k)
    (σ : Density (l+k)) (hσ : IsPureQuasifree σ) (hMarginal : prefixRestriction k l σ=ρ) :
    ∃ τ : Density (L+k),IsPureQuasifree τ ∧ prefixRestriction k L τ=ρ := by
  let m := L-l
  have hcount : m+(l+k)=L+k := by dsimp [m]; omega
  obtain ⟨τ,ψ,hτ,hOld,hProduct⟩ := exists_pure_quasifree_padding (l+k) m σ hσ
  refine ⟨modeCountCast hcount τ,modeCountCast_isPureQuasifree hcount τ hτ,?_⟩
  have hρ : IsQuasifree ρ := hMarginal ▸ isQuasifree_prefixRestriction k l σ hσ.1
  apply quasifree_eq_of_covariance _ ρ
    (isQuasifree_prefixRestriction k L _ (modeCountCast_isQuasifree hcount τ hτ.1)) hρ
  intro a b
  rw [prefixRestriction_covariance,modeCountCast_covariance]
  have hi (a : MajoranaIndex k) :
      (Fin.cast hcount.symm (prefixIndex k L a.1),a.2) =
        (prefixIndex (l+k) m (prefixIndex k l a.1),a.2) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [Fin.val_cast,prefixIndex_val]
    · rfl
  rw [hi a,hi b,← prefixRestriction_covariance (l+k) m τ
      (prefixIndex k l a.1,a.2) (prefixIndex k l b.1,b.2),hOld,
    ← prefixRestriction_covariance k l σ a b,hMarginal]

/-- Every raw finite Wick state has actual pure Gaussian purifications at all
auxiliary counts at least the number of physical modes. -/
theorem exists_quasifree_purification_of_le (n M : ℕ) (hsize : n≤M)
    (ρ : Density n) (hρ : IsQuasifree ρ) :
    ∃ σ : Density (M+n),IsPureQuasifree σ ∧ prefixRestriction n M σ=ρ := by
  obtain ⟨σ,hσ,hm⟩ := exists_quasifree_purification n ρ hρ
  exact exists_purifier_of_auxiliary_le n n M hsize ρ σ hσ hm

end Gaussian.Physical.Fermion
