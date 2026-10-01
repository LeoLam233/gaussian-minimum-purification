import Gaussian.Physical.Fermion.PairedCovariance
import Gaussian.Entropy.Compression
import Gaussian.Phase.Restriction
import Gaussian.Phase.CompressionAdaptation

/-! Actual CAR entropy and adapted positive-amplitude compression.
All state entropy is the existing density von Neumann entropy. -/
set_option autoImplicit false
noncomputable section
open Module Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- Every constructed skew adaptation of the actual trace covariance gives the
same physical entropy. Positive amplitudes and repeated/zero endpoints are proved,
not attached to an assumed physical spectrum. -/
theorem quasifree_entropy_of_adaptation {n : ℕ} (ρ : Density n) (hρ : IsQuasifree ρ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (hn : finrank ℝ (CoefficientSpace n) = 2*n) :
    Sᵥₙ ρ = Gaussian.Entropy.realListCost Gaussian.Entropy.fermion
      (d.positive.isSymmetric.eigenvalues hn) := by
  obtain ⟨b⟩ := exists_pairedEigenframe_dim n (CoefficientSpace n) hn
    d.complexStructure d.K d.positive.isSymmetric d.commute
  have hlo (i : Fin n) : 0 ≤ b.value i := by
    apply b.value_ge 0
    intro x
    simpa only [zero_mul] using d.positive.inner_nonneg_right x
  have hhi (i : Fin n) : b.value i ≤ 1 := by
    have h := (d.one_sub_positive (covarianceGenerator_contraction ρ)).inner_nonneg_left (b.basis (i,0))
    change 0 ≤ ⟪b.basis (i,0)-d.K (b.basis (i,0)),b.basis (i,0)⟫ at h
    rw [b.eigen,inner_sub_left,real_inner_smul_left,b.basis.inner_eq_ite] at h
    simpa using h
  let ht : ∀ i,b.value i ∈ Set.Icc (-1:ℝ) 1 := fun i => ⟨by linarith [hlo i],hhi i⟩
  have hs : Sᵥₙ ρ = ∑ i, Gaussian.Entropy.fermion (b.value i) := by
    apply quasifree_entropy_of_covariance_normal_form n ρ hρ b.value ht (frameRotation b)
    intro a c
    have h := frameRotation_covarianceForm ρ b d.factor ht
      ((frameRotation b).symm (coefficientBasis n a)) ((frameRotation b).symm (coefficientBasis n c))
    simpa only [LinearIsometryEquiv.apply_symm_apply,covarianceForm_basis,
      LinearIsometryEquiv.inv_def] using h
  rw [hs]
  have hp := paired_half_spectral_sum b d.positive.isSymmetric Gaussian.Entropy.fermion
  simpa only [Gaussian.Entropy.realListCost, one_div, div_eq_mul_inv, mul_comm, one_mul] using hp.symm

theorem quasifree_entropy_of_adaptation_dim {n m : ℕ} (ρ : Density n) (hρ : IsQuasifree ρ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (hn : finrank ℝ (CoefficientSpace n) = m) :
    Sᵥₙ ρ = Gaussian.Entropy.realListCost Gaussian.Entropy.fermion
      (d.positive.isSymmetric.eigenvalues hn) := by
  have hm : m=2*n := by simpa [CoefficientSpace,MajoranaIndex,Nat.mul_comm] using hn.symm
  cases hm
  exact quasifree_entropy_of_adaptation ρ hρ d hn

theorem quasifree_entropy_of_isometry_adaptation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {k : ℕ} (σ : Density k) (hσ : IsQuasifree σ)
    {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] E)
    (hT : ∀ x,e (covarianceGenerator σ x)=T (e x)) (hE : finrank ℝ E=2*k) :
    Sᵥₙ σ = Gaussian.Entropy.realListCost Gaussian.Entropy.fermion
      (d.positive.isSymmetric.eigenvalues hE) := by
  have hk : finrank ℝ (CoefficientSpace k)=2*k := by simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
  rw [quasifree_entropy_of_adaptation σ hσ (d.isometryTransport e _ hT) hk,
    d.isometryTransport_eigenvalues e _ hT hE hk]

/-- Actual density entropies obey the geometric comparison whenever their
independently defined CAR generators are related by the genuine selected cut. -/
theorem quasifree_entropy_comparison_of_compression {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (U : Submodule ℝ (CoefficientSpace n)) (hU : d.complexStructure.IsInvariant U)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] U)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) U (e x)) :
    Sᵥₙ σ ≤ Sᵥₙ ρ := by
  have hk : finrank ℝ U=2*k := by
    rw [← e.toLinearEquiv.finrank_eq]
    simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
  have hn : finrank ℝ (CoefficientSpace n)=finrank ℝ Uᗮ+2*k := by
    have h := U.finrank_add_finrank_orthogonal
    omega
  rw [quasifree_entropy_of_isometry_adaptation σ hσ (d.compressed U hU) e hT hk,
    quasifree_entropy_of_adaptation_dim ρ hρ d hn]
  exact Gaussian.Entropy.fermion_compression_comparison d.positive
    (d.one_sub_positive (covarianceGenerator_contraction ρ)) U hn hk

end Gaussian.Physical.Fermion
