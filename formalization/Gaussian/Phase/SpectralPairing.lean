import Gaussian.Phase.Restriction
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! Multiplicity-correct real spectral identifications. -/
noncomputable section
open Module Module.End
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A real complex structure forces even real dimension, including dimension zero. -/
theorem even_finrank_of_square_neg (J : E →ₗ[ℝ] E) (hJ : ∀ x, J (J x) = -x) :
    Even (finrank ℝ E) := by
  have hsq : J*J = -LinearMap.id := by ext x; exact hJ x
  have hd := congrArg LinearMap.det hsq
  rw [map_mul,← neg_one_smul ℝ (LinearMap.id : E →ₗ[ℝ] E),LinearMap.det_smul,
    LinearMap.det_id,mul_one] at hd
  rcases Nat.even_or_odd (finrank ℝ E) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hd
    nlinarith [sq_nonneg (LinearMap.det J)]

namespace OrthogonalComplexStructure
variable (J : OrthogonalComplexStructure E)
include J

theorem even_finrank : Even (finrank ℝ E) :=
  even_finrank_of_square_neg J.linear J.square_neg

/-- Eigenspaces of any commuting real operator are invariant under J. -/
theorem eigenspace_invariant (K : E →ₗ[ℝ] E) (hK : ∀ x, J (K x) = K (J x)) (a : ℝ) :
    J.IsInvariant (eigenspace K a) := by
  intro x hx
  rw [mem_eigenspace_iff] at hx ⊢
  rw [← hK,hx,J.apply_smul]

/-- Every eigenvalue has even geometric multiplicity; no simplicity hypothesis. -/
theorem even_eigenspace (K : E →ₗ[ℝ] E) (hK : ∀ x, J (K x) = K (J x)) (a : ℝ) :
    Even (finrank ℝ (eigenspace K a)) :=
  (J.restrict (eigenspace K a) (J.eigenspace_invariant K hK a)).even_finrank

/-- For symmetric K, the sorted spectral list contains each value an even
number of times, so the doubled real spectrum counts whole modes. -/
theorem even_eigenvalue_multiplicity (K : E →ₗ[ℝ] E) (hKs : K.IsSymmetric)
    (hK : ∀ x, J (K x) = K (J x)) {n : ℕ} (hn : finrank ℝ E = n) (a : ℝ) :
    Even (Finset.card {i : Fin n | hKs.eigenvalues hn i = a}) := by
  have hc : Finset.card {i : Fin n | hKs.eigenvalues hn i = a} =
      finrank ℝ (eigenspace K a) := by simpa using hKs.card_filter_eigenvalues_eq hn a
  rw [hc]
  exact J.even_eigenspace K hK a

end OrthogonalComplexStructure

/-- An independently given decreasing orthonormal eigenframe identifies the
library's sorted eigenvalues, preserving all repeated values. -/
theorem eigenvalues_eq_of_sorted_eigenbasis {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (b : OrthonormalBasis (Fin n) ℝ E)
    (a : Fin n → ℝ) (ha : Antitone a) (he : ∀ i, T (b i) = a i • b i) :
    hT.eigenvalues hn = a := by
  have hm : T.toMatrix b.toBasis b.toBasis = Matrix.diagonal a := by
    ext i j
    simp only [LinearMap.toMatrix_apply,he,map_smul,OrthonormalBasis.coe_toBasis,
      Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul,Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hr : T.charpoly.roots = Multiset.map a Finset.univ.val := by
    rw [← T.charpoly_toMatrix b.toBasis,hm,Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero])]
    simp
  rw [← List.ofFn_inj,← hT.sort_roots_charpoly_eq_eigenvalues hn,hr]
  simp only [Multiset.map_map,Function.comp_def,RCLike.re_to_real]
  rw [Fin.univ_val_map,Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp only [decide_eq_true_eq,← List.sortedGE_iff_pairwise]
  exact ha.sortedGE_ofFn

/-- For a positive K, any operator whose Gram operator is K² has exactly the
sorted K-spectrum as its independently defined singular-value list. -/
theorem singularValues_eq_eigenvalues_of_gram (T K : E →ₗ[ℝ] E) (hK : K.IsPositive)
    (hGram : T.adjoint ∘ₗ T = K*K) {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    T.singularValues i = hK.isSymmetric.eigenvalues hn i := by
  let a := hK.isSymmetric.eigenvalues hn
  have ha : Antitone (fun i => (a i)^2) := by
    intro i j hij
    exact (sq_le_sq₀ (hK.nonneg_eigenvalues hn j) (hK.nonneg_eigenvalues hn i)).mpr
      (hK.isSymmetric.eigenvalues_antitone hn hij)
  have he : ∀ j, (T.adjoint ∘ₗ T) (hK.isSymmetric.eigenvectorBasis hn j) =
      (a j)^2 • hK.isSymmetric.eigenvectorBasis hn j := by
    intro j
    rw [hGram]
    change K (K (hK.isSymmetric.eigenvectorBasis hn j)) = _
    rw [hK.isSymmetric.apply_eigenvectorBasis,map_smul,hK.isSymmetric.apply_eigenvectorBasis,
      smul_smul]
    simp [a,pow_two]
  have hs := eigenvalues_eq_of_sorted_eigenbasis T.isSymmetric_adjoint_comp_self hn
    (hK.isSymmetric.eigenvectorBasis hn) (fun j => (a j)^2) ha he
  rw [T.singularValues_fin hn,hs,Real.sqrt_sq_eq_abs,abs_of_nonneg (hK.nonneg_eigenvalues hn i)]

/-- The ordinary independently defined real singular spectrum of JK equals
that of the positive amplitude K; this is not a definition of singular values. -/
theorem singularValues_eq_amplitude (J : OrthogonalComplexStructure E)
    (T K : E →ₗ[ℝ] E) (hK : K.IsPositive) (hT : ∀ x, T x = J (K x))
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    T.singularValues i = hK.isSymmetric.eigenvalues hn i := by
  apply singularValues_eq_eigenvalues_of_gram T K hK _ hn i
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  change ⟪x,T.adjoint (T y)⟫ = ⟪x,K (K y)⟫
  rw [T.adjoint_inner_right,hT,hT,J.inner_map_map,hK.isSymmetric]

/-- Positivity survives the genuine metric compression. -/
theorem compression_positive (K : E →ₗ[ℝ] E) (hK : K.IsPositive) (U : Submodule ℝ E) :
    (Gaussian.Spectral.compression K U).IsPositive := by
  refine ⟨Gaussian.Spectral.compression_symmetric hK.isSymmetric U,?_⟩
  intro x
  change 0 ≤ ⟪Gaussian.Spectral.compression K U x,x⟫
  rw [real_inner_comm,Gaussian.Spectral.inner_compression]
  exact hK.inner_nonneg_right x

/-- C3-F spectral identification for the actual restricted covariance,
including every repeated or zero singular value. -/
theorem fermionic_restricted_singularValues {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (U : Submodule ℝ E) (hU : d.complexStructure.IsInvariant U)
    {n : ℕ} (hn : finrank ℝ U = n) (i : Fin n) :
    (formGenerator ((skewCovarianceForm T).restrict U)).singularValues i =
      (compression_positive d.K d.positive U).isSymmetric.eigenvalues hn i := by
  exact singularValues_eq_amplitude (d.complexStructure.restrict U hU)
    (formGenerator ((skewCovarianceForm T).restrict U)) (Gaussian.Spectral.compression d.K U)
    (compression_positive d.K d.positive U) (fermionic_restricted_factor d U hU) hn i

/-- Every singular value in the actual retained covariance has even
multiplicity in its finite real list. -/
theorem fermionic_restricted_even_multiplicity {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (U : Submodule ℝ E) (hU : d.complexStructure.IsInvariant U)
    {n : ℕ} (hn : finrank ℝ U = n) (a : ℝ) :
    Even (Finset.card {i : Fin n |
      (formGenerator ((skewCovarianceForm T).restrict U)).singularValues i = a}) := by
  simp_rw [fermionic_restricted_singularValues d U hU hn]
  exact (d.complexStructure.restrict U hU).even_eigenvalue_multiplicity _
    (compression_positive d.K d.positive U).isSymmetric
    (d.complexStructure.compression_commute U hU d.K d.commute) hn a


end Gaussian.Phase
