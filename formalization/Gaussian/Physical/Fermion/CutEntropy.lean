import Gaussian.Physical.Fermion.StateTopology

/-! Genuine partial-trace entropy objectives after actual CAR-implemented
orthogonal mode selection, including changes of finite mode-count notation. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

/-- Transport solely along an equality of the number of complete modes. -/
def modeCountCast {n m : ℕ} (h : n=m) (ρ : Density n) : Density m := h ▸ ρ

@[fun_prop] theorem continuous_modeCountCast {n m : ℕ} (h : n=m) :
    Continuous (modeCountCast h) := by
  subst m
  exact continuous_id

set_option backward.isDefEq.respectTransparency false in
@[fun_prop] theorem continuous_unitaryState (n : ℕ)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) : Continuous (fun ρ : Density n => ρ.uConj U) := by
  rw [continuous_induced_rng,continuous_induced_rng]
  change Continuous (fun ρ : Density n => (U : Operator n)*ρ.m*(U : Operator n)ᴴ)
  fun_prop

/-- Actual restriction after a fixed unitary mode selection and a harmless
mode-count equality.  Physical CAR selections are accompanied by Implements. -/
def selectedRestriction {n : ℕ} (k l : ℕ) (h : n=l+k)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (ρ : Density n) : Density k :=
  prefixRestriction k l (modeCountCast h (ρ.uConj U))

@[fun_prop] theorem continuous_selectedRestriction {n : ℕ} (k l : ℕ) (h : n=l+k)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) : Continuous (selectedRestriction k l h U) :=
  (continuous_prefixRestriction k l).comp
    ((continuous_modeCountCast h).comp (continuous_unitaryState n U))

@[fun_prop] theorem continuous_selectedEntropy {n : ℕ} (k l : ℕ) (h : n=l+k)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) :
    Continuous (fun ρ : Density n => Sᵥₙ (selectedRestriction k l h U ρ)) :=
  Sᵥₙ_continuous.comp (continuous_selectedRestriction k l h U)

theorem selectedRestriction_isQuasifree {n : ℕ} (k l : ℕ) (h : n=l+k)
    (ρ : Density n) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    IsQuasifree (selectedRestriction k l h U ρ) := by
  subst n
  exact isQuasifree_orthogonalRestriction k l ρ hρ R U hU

/-- The actual entropy of every complete-mode orthogonal cut is its independently
defined Hermitian covariance spectral cost, by proved raw Wick semantics. -/
theorem selectedEntropy_eq_hermitianCost {n : ℕ} (k l : ℕ) (h : n=l+k)
    (ρ : Density n) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    Sᵥₙ (selectedRestriction k l h U ρ) =
      Gaussian.Attainment.fermionHermitianCost
        (covarianceHermitianMat (selectedRestriction k l h U ρ)) :=
  quasifree_entropy_eq_hermitianCost k _ (selectedRestriction_isQuasifree k l h ρ hρ R U hU)

/-- Every nonempty fixed-size actual Gaussian purification problem has an
entropy-minimizing state for any fixed genuine complete-mode cut. -/
theorem exists_minimum_selectedEntropy (physical auxiliary k l : ℕ)
    (h : auxiliary+physical=l+k) (ρ : Density physical)
    (hnonempty : ∃ σ : Density (auxiliary+physical),
      IsPureQuasifree σ ∧ prefixRestriction physical auxiliary σ=ρ)
    (U : Matrix.unitaryGroup (Occupation (auxiliary+physical)) ℂ) :
    ∃ σ : Density (auxiliary+physical),IsPureQuasifree σ ∧
      prefixRestriction physical auxiliary σ=ρ ∧
      ∀ τ : Density (auxiliary+physical),IsPureQuasifree τ →
        prefixRestriction physical auxiliary τ=ρ →
        Sᵥₙ (selectedRestriction k l h U σ)≤Sᵥₙ (selectedRestriction k l h U τ) :=
  exists_minimum_quasifreePurifiers physical auxiliary ρ hnonempty _
    (continuous_selectedEntropy k l h U)

end Gaussian.Physical.Fermion
