import Gaussian.Entropy.Comparison
import Gaussian.Spectral.Bounds
import Gaussian.Spectral.TraceSupport

/-! Entropy comparison and exact rigidity for genuine self-adjoint compressions.
These are coefficient-operator statements; physical Gaussian entropy still requires its bridge. -/
noncomputable section
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

private theorem boson_domains (hK : K.IsSymmetric) (hd : (K-LinearMap.id).IsPositive)
    (U : Submodule ℝ E) {n m : ℕ} (hn : Module.finrank ℝ E = n)
    (hm : Module.finrank ℝ U = m) :
    (∀ i, 1 ≤ hK.eigenvalues hn i) ∧
    (∀ i, 1 ≤ (compression_symmetric hK U).eigenvalues hm i) := by
  exact ⟨eigenvalue_ge_of_quadratic hK hn 1 (lower_quadratic_of_defect hd),
    eigenvalue_ge_of_quadratic (compression_symmetric hK U) hm 1
      (compression_lower_quadratic U 1 (lower_quadratic_of_defect hd))⟩

private theorem fermion_domains (hK : K.IsPositive) (hd : (LinearMap.id-K).IsPositive)
    (U : Submodule ℝ E) {n m : ℕ} (hn : Module.finrank ℝ E = n)
    (hm : Module.finrank ℝ U = m) :
    (∀ i, hK.isSymmetric.eigenvalues hn i ∈ Set.Icc (0:ℝ) 1) ∧
    (∀ i, (compression_symmetric hK.isSymmetric U).eigenvalues hm i ∈ Set.Icc (0:ℝ) 1) := by
  have hzero : ∀ x, 0 * ‖x‖^2 ≤ ⟪x,K x⟫ := by
    intro x; simpa using hK.inner_nonneg_right x
  exact ⟨fun i => ⟨eigenvalue_ge_of_quadratic hK.isSymmetric hn 0 hzero i,
      eigenvalue_le_of_quadratic hK.isSymmetric hn 1 (upper_quadratic_of_defect hd) i⟩,
    fun i => ⟨eigenvalue_ge_of_quadratic (compression_symmetric hK.isSymmetric U) hm 0
      (compression_lower_quadratic U 0 hzero) i,
      eigenvalue_le_of_quadratic (compression_symmetric hK.isSymmetric U) hm 1
      (compression_upper_quadratic U 1 (upper_quadratic_of_defect hd)) i⟩⟩

theorem boson_compression_comparison (hK : K.IsSymmetric)
    (hd : (K-LinearMap.id).IsPositive) (U : Submodule ℝ E)
    {m c : ℕ} (hn : Module.finrank ℝ E = m+c) (hm : Module.finrank ℝ U = m) :
    realListCost boson ((compression_symmetric hK U).eigenvalues hm) ≤
      realListCost boson (hK.eigenvalues hn) := by
  have hdom := boson_domains hK hd U hn hm
  apply boson_prefix_comparison _ _ hdom.1 hdom.2
  intro i
  exact compression_eigenvalue_le hK U hn hm (by omega) i

theorem fermion_compression_comparison (hK : K.IsPositive)
    (hd : (LinearMap.id-K).IsPositive) (U : Submodule ℝ E)
    {c m : ℕ} (hn : Module.finrank ℝ E = c+m) (hm : Module.finrank ℝ U = m) :
    realListCost fermion ((compression_symmetric hK.isSymmetric U).eigenvalues hm) ≤
      realListCost fermion (hK.isSymmetric.eigenvalues hn) := by
  have hdom := fermion_domains hK hd U hn hm
  apply fermion_suffix_comparison _ _ hdom.1 hdom.2
  intro i
  have h := le_compression_eigenvalue hK.isSymmetric U hn hm (by omega) i
  have he : (⟨i.val + (c+m-m),by omega⟩ : Fin (c+m)) = Fin.natAdd c i := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega
  simpa only [he] using h

/-- Equality forces exact endpoint identity on the discarded space and zero cross block. -/
theorem boson_compression_rigidity (hK : K.IsSymmetric)
    (hd : (K-LinearMap.id).IsPositive) (U : Submodule ℝ E)
    {m c : ℕ} (hn : Module.finrank ℝ E = m+c) (hm : Module.finrank ℝ U = m)
    (he : realListCost boson ((compression_symmetric hK U).eigenvalues hm) =
      realListCost boson (hK.eigenvalues hn)) :
    (∀ x ∈ Uᗮ, K x = x) ∧ (∀ x ∈ Uᗮ, ∀ y ∈ U, ⟪K y,x⟫ = 0) := by
  have hdom := boson_domains hK hd U hn hm
  have hr := boson_prefix_rigidity _ _ hdom.1 hdom.2
    (fun i => compression_eigenvalue_le hK U hn hm (by omega) i) he
  have hc : Module.finrank ℝ Uᗮ = c := by
    have h := U.finrank_add_finrank_orthogonal
    omega
  have ht : LinearMap.trace ℝ E K = LinearMap.trace ℝ U (compression K U) +
      (Module.finrank ℝ Uᗮ : ℝ) := by
    rw [hK.trace_eq_sum_eigenvalues hn,
      (compression_symmetric hK U).trace_eq_sum_eigenvalues hm, Fin.sum_univ_add, hc]
    simp only [hr.1, hr.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq]
  have hh := lower_endpoint_trace_rigidity K U hd ht
  exact ⟨hh,cross_block_zero_of_endpoint K hK U hh⟩

/-- Fermionic equality uses I−K, rather than K−I. -/
theorem fermion_compression_rigidity (hK : K.IsPositive)
    (hd : (LinearMap.id-K).IsPositive) (U : Submodule ℝ E)
    {c m : ℕ} (hn : Module.finrank ℝ E = c+m) (hm : Module.finrank ℝ U = m)
    (he : realListCost fermion ((compression_symmetric hK.isSymmetric U).eigenvalues hm) =
      realListCost fermion (hK.isSymmetric.eigenvalues hn)) :
    (∀ x ∈ Uᗮ, K x = x) ∧ (∀ x ∈ Uᗮ, ∀ y ∈ U, ⟪K y,x⟫ = 0) := by
  have hdom := fermion_domains hK hd U hn hm
  have hib : ∀ i : Fin m, hK.isSymmetric.eigenvalues hn (Fin.natAdd c i) ≤
      (compression_symmetric hK.isSymmetric U).eigenvalues hm i := by
    intro i
    have h := le_compression_eigenvalue hK.isSymmetric U hn hm (by omega) i
    have hej : (⟨i.val + (c+m-m),by omega⟩ : Fin (c+m)) = Fin.natAdd c i := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    simpa only [hej] using h
  have hr := fermion_suffix_rigidity _ _ hdom.1 hdom.2 hib he
  have hc : Module.finrank ℝ Uᗮ = c := by
    have h := U.finrank_add_finrank_orthogonal
    omega
  have ht : LinearMap.trace ℝ E K = LinearMap.trace ℝ U (compression K U) +
      (Module.finrank ℝ Uᗮ : ℝ) := by
    rw [hK.isSymmetric.trace_eq_sum_eigenvalues hn,
      (compression_symmetric hK.isSymmetric U).trace_eq_sum_eigenvalues hm,
      Fin.sum_univ_add, hc]
    simp only [hr.1, hr.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq]
    ring
  have hh := upper_endpoint_trace_rigidity K U hd ht
  exact ⟨hh,cross_block_zero_of_endpoint K hK.isSymmetric U hh⟩
end Gaussian.Entropy
