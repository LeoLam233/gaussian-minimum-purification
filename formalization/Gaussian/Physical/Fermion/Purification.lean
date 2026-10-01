import Gaussian.Physical.Fermion.PurificationTransport
import Gaussian.Physical.Fermion.RealSkewMatrix
import Gaussian.Physical.Fermion.DoubledIndices
import Gaussian.Physical.Fermion.GaussianClosure

/-! Actual finite CAR quasifree purification.  The construction realizes an
explicit pure doubled covariance, then identifies its genuine partial trace
using the raw Wick uniqueness theorem.  Pure endpoints and empty systems remain. -/
noncomputable section
open Gaussian.Phase
open scoped Matrix
namespace Gaussian.Physical.Fermion

/-- Reindexing a raw doubled complex structure yields an actual pure CAR state. -/
theorem realize_doubled_pure_matrix (n : ℕ)
    (M : Matrix (MajoranaIndex n ⊕ MajoranaIndex n) (MajoranaIndex n ⊕ MajoranaIndex n) ℝ)
    (hSkew : Mᵀ = -M) (hPure : M*M = -1) :
    ∃ σ : Density (n+n),IsPureQuasifree σ ∧
      generatorMatrix σ = Matrix.reindexAlgEquiv ℝ ℝ (doubledMajoranaEquiv n) M := by
  let N := Matrix.reindexAlgEquiv ℝ ℝ (doubledMajoranaEquiv n) M
  have hNskew : Nᵀ = -N := reindex_transpose_neg M hSkew _
  have hNsquare : N*N = -1 := by
    have h := congrArg (Matrix.reindexAlgEquiv ℝ ℝ (doubledMajoranaEquiv n)) hPure
    simpa only [map_mul,map_neg,map_one] using h
  obtain ⟨σ,hσ,hΓ⟩ := realize_pure_skew (n+n) (Matrix.toEuclideanLin N)
    (realMatrix_operator_skew N hNskew) (realMatrix_operator_square_neg N hNsquare)
  refine ⟨σ,hσ,?_⟩
  apply Matrix.toEuclideanLin.injective
  exact hΓ

/-- Every raw parity-invariant quasifree density has an actual pure quasifree
purification on n physical and n auxiliary complete modes. -/
theorem exists_quasifree_purification (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    ∃ σ : Density (n+n),IsPureQuasifree σ ∧ prefixRestriction n n σ = ρ := by
  obtain ⟨t,ht,R,U,hpos,hU,he⟩ := exists_quasifree_state_normal_form n ρ hρ
  obtain ⟨σ,hσ,hM⟩ := realize_doubled_pure_matrix n (rotatedPurificationBlock n t ht R)
    (rotatedPurificationBlock_transpose n t ht R) (rotatedPurificationBlock_square n t ht R)
  refine ⟨σ,hσ,quasifree_eq_of_covariance _ ρ
    (isQuasifree_prefixRestriction n n σ hσ.1) hρ ?_⟩
  intro a b
  rw [prefixRestriction_covariance]
  have hab := congrFun₂ hM (prefixIndex n n a.1,a.2) (prefixIndex n n b.1,b.2)
  change -covariance σ (prefixIndex n n a.1,a.2) (prefixIndex n n b.1,b.2) =
    rotatedPurificationBlock n t ht R
      ((doubledMajoranaEquiv n).symm (prefixIndex n n a.1,a.2))
      ((doubledMajoranaEquiv n).symm (prefixIndex n n b.1,b.2)) at hab
  rw [doubledMajoranaEquiv_symm_prefix,doubledMajoranaEquiv_symm_prefix,
    rotatedPurificationBlock_physical n t ht R U hU,← he] at hab
  exact neg_injective hab

end Gaussian.Physical.Fermion
