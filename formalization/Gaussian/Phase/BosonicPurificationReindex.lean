import Gaussian.Phase.BosonicPurificationCost

/-! Index changes preserve the independently constructed Hermitian-pair cost.
This allows genuine finite frame cuts to use their natural disjoint-sum index
without assuming that their spectrum already has a paired indexing. -/
noncomputable section
open Module
namespace Gaussian.Phase

section Matrices
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Both raw forms are reindexed before the independent Hermitian generator is built. -/
theorem bosonPairHermitian_reindex (V O : HermitianMat ι ℂ) (q : ι ≃ κ) :
    Gaussian.Attainment.bosonPairHermitian (V.reindex q) (O.reindex q) =
      (Gaussian.Attainment.bosonPairHermitian V O).reindex q := by
  apply HermitianMat.ext
  simp only [Gaussian.Attainment.bosonPairHermitian,HermitianMat.sqrt,
    HermitianMat.cfc_reindex,HermitianMat.conj_apply_mat,HermitianMat.mat_neg,
    HermitianMat.mat_inv,HermitianMat.mat_reindex,Matrix.inv_reindex,
    Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply]
  change (V.cfc Real.sqrt).mat.submatrix q.symm q.symm *
      (-O.mat⁻¹).submatrix q.symm q.symm *
      (V.cfc Real.sqrt).mat.conjTranspose.submatrix q.symm q.symm = _
  rw [Matrix.submatrix_mul_equiv _ _ q.symm q.symm q.symm,
    Matrix.submatrix_mul_equiv _ _ q.symm q.symm q.symm]

/-- The half-trace functional is invariant under an arbitrary finite index equivalence. -/
theorem bosonPairCost_reindex (V O : HermitianMat ι ℂ) (q : ι ≃ κ) :
    Gaussian.Attainment.bosonPairCost (V.reindex q) (O.reindex q) =
      Gaussian.Attainment.bosonPairCost V O := by
  simp only [Gaussian.Attainment.bosonPairCost,bosonPairHermitian_reindex,
    Gaussian.Attainment.bosonHermitianCost,HermitianMat.cfc_reindex,HermitianMat.trace_reindex]

end Matrices

section Forms
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem bosonFormCost_reindex (e : Basis ι ℝ E) (q : ι ≃ κ)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt) :
    bosonFormCost (e.reindex q) V Ω hV hΩ = bosonFormCost e V Ω hV hΩ := by
  have hv : Gaussian.Spectral.covarianceHermitianOfForm (e.reindex q) V hV =
      (Gaussian.Spectral.covarianceHermitianOfForm e V hV).reindex q := by
    apply HermitianMat.ext
    ext i j
    simp only [Gaussian.Spectral.covarianceHermitianOfForm,HermitianMat.mat_mk,
      HermitianMat.reindex,HermitianMat.mat_reindex,Matrix.reindex_apply,Matrix.submatrix_apply,
      Gaussian.Spectral.complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,Basis.reindex_apply]
  have ho : Gaussian.Spectral.commutatorHermitianOfForm (e.reindex q) Ω hΩ =
      (Gaussian.Spectral.commutatorHermitianOfForm e Ω hΩ).reindex q := by
    apply HermitianMat.ext
    ext i j
    simp only [Gaussian.Spectral.commutatorHermitianOfForm,HermitianMat.mat_mk,
      HermitianMat.reindex,HermitianMat.mat_reindex,Matrix.reindex_apply,Matrix.submatrix_apply,
      Gaussian.Spectral.complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,Basis.reindex_apply,
      Matrix.smul_apply]
  unfold bosonFormCost
  rw [hv,ho]
  exact bosonPairCost_reindex (Gaussian.Spectral.covarianceHermitianOfForm e V hV)
    (Gaussian.Spectral.commutatorHermitianOfForm e Ω hΩ) q

/-- A coefficient basis may have any finite index; the paired basis is an actual
Williamson witness, and never a prescribed spectrum in the objective definition. -/
theorem bosonFormCost_eq_canonical_general [FiniteDimensional ℝ E] {n : ℕ}
    (e : Basis ι ℝ E) (b : Basis (Fin n × Bool) ℝ E)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (hbV : ∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0)
    (hbΩ : ∀ i j, Ω (b i) (b j) = Gaussian.Spectral.canonicalModeSkew n i j) :
    bosonFormCost e V Ω hV hΩ = ∑ i, Gaussian.Entropy.boson (ν i) := by
  let q : ι ≃ (Fin n × Bool) := Fintype.equivOfCardEq
    ((Module.finrank_eq_card_basis e).symm.trans (Module.finrank_eq_card_basis b))
  rw [← bosonFormCost_reindex e q V Ω hV hΩ]
  exact bosonFormCost_eq_canonical (e.reindex q) b V Ω hV hΩ ν hν hbV hbΩ

/-- The mode index can itself be any finite type, including a sum used for
actual product covariances. The two displayed matrices are genuine coefficients. -/
theorem bosonFormCost_eq_sum_of_mode_basis [FiniteDimensional ℝ E]
    {η : Type*} [Fintype η] [DecidableEq η]
    (e : Basis ι ℝ E) (b : Basis (η × Bool) ℝ E)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (ν : η → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (hbV : ∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0)
    (hbΩ : ∀ i j, Ω (b i) (b j) =
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
        else (if j.2 then 1 else 0)) else 0) :
    bosonFormCost e V Ω hV hΩ = ∑ i, Gaussian.Entropy.boson (ν i) := by
  let q := Fintype.equivFin η
  let r := Equiv.prodCongr q (Equiv.refl Bool)
  have hc := bosonFormCost_eq_canonical_general e (b.reindex r) V Ω hV hΩ
    (fun i => ν (q.symm i)) (fun i => hν (q.symm i))
  have hv : ∀ i j, V ((b.reindex r) i) ((b.reindex r) j) =
      if i=j then ν (q.symm i.1) else 0 := by
    intro i j
    simp only [Basis.reindex_apply,hbV,r.symm.injective.eq_iff]
    rfl
  have ho : ∀ i j, Ω ((b.reindex r) i) ((b.reindex r) j) =
      Gaussian.Spectral.canonicalModeSkew (Fintype.card η) i j := by
    intro i j
    simp only [Basis.reindex_apply,hbΩ,Gaussian.Spectral.canonicalModeSkew,
      r,Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.refl_symm,Prod.map,
      Equiv.refl_apply,q.symm.injective.eq_iff]
  rw [hc hv ho]
  exact q.symm.sum_comp (fun i => Gaussian.Entropy.boson (ν i))

end Forms
end Gaussian.Phase
