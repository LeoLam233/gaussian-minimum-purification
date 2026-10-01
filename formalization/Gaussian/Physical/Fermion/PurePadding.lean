import Gaussian.Physical.Fermion.BlockIndices
import Gaussian.Physical.Fermion.Purification
import Gaussian.Physical.Fermion.Factorization

/-! Actual pure Gaussian extensions by independent pure covariance blocks.
No Gaussianity or marginal statement is supplied as a construction field. -/
noncomputable section
open scoped Matrix MState
namespace Gaussian.Physical.Fermion

theorem generatorMatrix_square_of_pure {n : ℕ} (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    generatorMatrix ρ * generatorMatrix ρ = -1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same,toEuclidean_generatorMatrix]
  simp only [map_neg,Matrix.toLpLin_one]
  apply LinearMap.ext
  intro v
  exact (quasifree_pure_iff_covariancePure n ρ hρ.1).mp hρ.2 v

theorem realize_block_pure_matrix (n m : ℕ)
    (M : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ)
    (hSkew : Mᵀ = -M) (hPure : M*M = -1) :
    ∃ σ : Density (m+n),IsPureQuasifree σ ∧
      generatorMatrix σ = Matrix.reindexAlgEquiv ℝ ℝ (blockMajoranaEquiv n m) M := by
  let N := Matrix.reindexAlgEquiv ℝ ℝ (blockMajoranaEquiv n m) M
  have hNskew : Nᵀ = -N := reindex_transpose_neg M hSkew _
  have hNsquare : N*N = -1 := by
    have h := congrArg (Matrix.reindexAlgEquiv ℝ ℝ (blockMajoranaEquiv n m)) hPure
    simpa only [map_mul,map_neg,map_one] using h
  obtain ⟨σ,hσ,hΓ⟩ := realize_pure_skew (m+n) (Matrix.toEuclideanLin N)
    (realMatrix_operator_skew N hNskew) (realMatrix_operator_square_neg N hNsquare)
  refine ⟨σ,hσ,?_⟩
  apply Matrix.toEuclideanLin.injective
  exact hΓ

/-- Raw direct sums of two pure covariance blocks are actual pure Gaussian
extensions, and their genuine old-state marginal is exactly recovered. -/
theorem exists_pure_block_extension (n m : ℕ) (ρ : Density n) (η : Density m)
    (hρ : IsPureQuasifree ρ) (hη : IsPureQuasifree η) :
    ∃ σ : Density (m+n),IsPureQuasifree σ ∧ prefixRestriction n m σ=ρ ∧
      generatorMatrix σ = Matrix.reindexAlgEquiv ℝ ℝ (blockMajoranaEquiv n m)
        (Matrix.fromBlocks (generatorMatrix ρ) 0 0 (generatorMatrix η)) := by
  let M := Matrix.fromBlocks (generatorMatrix ρ) 0 0 (generatorMatrix η)
  have hMskew : Mᵀ = -M := by
    simp only [M,Matrix.fromBlocks_transpose,generatorMatrix_transpose,Matrix.transpose_zero]
    ext a b
    cases a <;> cases b <;> simp [Matrix.fromBlocks]
  have hMsquare : M*M = -1 := by
    simp only [M,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,
      add_zero,generatorMatrix_square_of_pure ρ hρ,generatorMatrix_square_of_pure η hη]
    ext a b
    cases a <;> cases b <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  obtain ⟨σ,hσ,hM⟩ := realize_block_pure_matrix n m M hMskew hMsquare
  refine ⟨σ,hσ,quasifree_eq_of_covariance _ ρ
    (isQuasifree_prefixRestriction n m σ hσ.1) hρ.1 ?_,hM⟩
  intro a b
  rw [prefixRestriction_covariance]
  have hab := congrFun₂ hM (prefixIndex n m a.1,a.2) (prefixIndex n m b.1,b.2)
  change -covariance σ (prefixIndex n m a.1,a.2) (prefixIndex n m b.1,b.2) =
    M ((blockMajoranaEquiv n m).symm (prefixIndex n m a.1,a.2))
      ((blockMajoranaEquiv n m).symm (prefixIndex n m b.1,b.2)) at hab
  rw [blockMajoranaEquiv_symm_prefix,blockMajoranaEquiv_symm_prefix] at hab
  exact neg_injective hab

/-- A pure extension of an old pure state really factors as an ordinary density
product after the canonical occupation split; the extra state is itself pure. -/
theorem pure_extension_factors (n m : ℕ) (ρ : Density n) (σ : Density (m+n))
    (hρ : ∃ ψ,ρ=MState.pure ψ) (hσ : ∃ ψ,σ=MState.pure ψ)
    (hMarginal : prefixRestriction n m σ=ρ) :
    ∃ ψ : Ket (Occupation m),
      σ.relabel (occupationSplit n m).symm = ρ.prod (MState.pure ψ) := by
  let τ := σ.relabel (occupationSplit n m).symm
  have hp : ∃ ψ,τ=MState.pure ψ := by
    obtain ⟨ψ,rfl⟩ := hσ
    exact MState.relabel_pure_exists ψ _
  have hleft : τ.traceRight=ρ := hMarginal
  have hfac := pure_density_factors_of_pure_left τ hp (hleft ▸ hρ)
  have hpurity := (MState.pure_iff_purity_one τ).mp hp
  rw [hfac,MState.purity_prod,hleft,(MState.pure_iff_purity_one ρ).mp hρ,one_mul] at hpurity
  obtain ⟨ψ,hψ⟩ := (MState.pure_iff_purity_one τ.traceLeft).mpr hpurity
  refine ⟨ψ,?_⟩
  change τ=ρ.prod (MState.pure ψ)
  rw [hfac,hleft,hψ]

/-- Arbitrarily many complete pure auxiliary modes can be added to an actual
pure Wick density, preserving its old state exactly and adding a pure factor. -/
theorem exists_pure_quasifree_padding (n m : ℕ) (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    ∃ (σ : Density (m+n)) (ψ : Ket (Occupation m)),IsPureQuasifree σ ∧
      prefixRestriction n m σ=ρ ∧
      σ.relabel (occupationSplit n m).symm = ρ.prod (MState.pure ψ) := by
  let t : Fin m → ℝ := fun _ => 1
  have ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1 := by intro i; simp [t]
  have hη : IsPureQuasifree (thermal m t ht) :=
    ⟨thermal_isQuasifree m t ht,(thermal_pure_iff_endpoints m t ht).mpr (fun _ => Or.inl rfl)⟩
  obtain ⟨σ,hσ,hm,hM⟩ := exists_pure_block_extension n m ρ (thermal m t ht) hρ hη
  obtain ⟨ψ,hψ⟩ := pure_extension_factors n m ρ σ hρ.2 hσ.2 hm
  exact ⟨σ,ψ,hσ,hm,hψ⟩

end Gaussian.Physical.Fermion
