import Gaussian.Spectral.Interlacing
import Gaussian.Phase.PositiveTools
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Exact support rigidity. A zero positive compression trace annihilates the
whole subspace in the ambient operator, including all cross blocks. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Gaussian.Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}

/-- The trace-zero criterion is for the genuine compression, not a stipulated spectrum. -/
theorem positive_compression_trace_zero (hH : H.IsPositive) (D : Submodule ℝ E)
    (ht : LinearMap.trace ℝ D (compression H D) = 0) :
    ∀ x ∈ D, H x = 0 := by
  let b := stdOrthonormalBasis ℝ D
  have hs : ∑ i, ⟪(b i : E),H (b i : E)⟫ = 0 := by
    simpa only [LinearMap.trace_eq_sum_inner _ b, inner_compression] using ht
  have hz : ∀ i, H (b i : E) = 0 := by
    intro i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hH.inner_nonneg_right (b j : E))).mp hs i (Finset.mem_univ i)
    apply (Gaussian.Phase.positive_inner_eq_zero_iff hH (b i : E)).mp
    simpa only [hH.isSymmetric (b i : E) (b i : E)] using hzero
  intro x hx
  let y : D := ⟨x,hx⟩
  have he := congrArg (fun v : D => H (v : E)) (b.sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hz, smul_zero,
    Finset.sum_const_zero] at he
  exact he.symm

/-- Endpoint-amplitude rigidity for either sign: prove positivity of the defect,
then a zero discarded trace gives exact full-vector vanishing. -/
theorem positive_defect_cross_block_zero (hH : H.IsPositive) (D : Submodule ℝ E)
    (ht : LinearMap.trace ℝ D (compression H D) = 0) :
    (∀ x ∈ D, H x = 0) ∧ (∀ x ∈ D, ∀ y : E, ⟪H y,x⟫ = 0) := by
  have hh := positive_compression_trace_zero hH D ht
  refine ⟨hh,?_⟩
  intro x hx y
  rw [hH.isSymmetric, hh x hx, inner_zero_right]

/-- Trace splits between genuine orthogonal compressions, even when T has cross blocks. -/
theorem trace_eq_compression_add (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) :
    LinearMap.trace ℝ E T = LinearMap.trace ℝ U (compression T U) +
      LinearMap.trace ℝ Uᗮ (compression T Uᗮ) := by
  let bU := stdOrthonormalBasis ℝ U
  let bD := stdOrthonormalBasis ℝ Uᗮ
  rw [LinearMap.trace_eq_sum_inner T ((bU.prod bD).map U.orthogonalDecomposition.symm),
    LinearMap.trace_eq_sum_inner _ bU, LinearMap.trace_eq_sum_inner _ bD,
    Fintype.sum_sum_type]
  simp only [OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
    Sum.elim_inl, Sum.elim_inr, Function.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, Submodule.orthogonalDecomposition_symm_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, Submodule.coe_zero, add_zero, zero_add,
    inner_compression]

@[simp] theorem compression_sub (S T : E →ₗ[ℝ] E) (U : Submodule ℝ E) :
    compression (S-T) U = compression S U - compression T U := by
  ext x
  simp [compression]

@[simp] theorem compression_id (U : Submodule ℝ E) :
    compression (LinearMap.id : E →ₗ[ℝ] E) U = LinearMap.id := by
  ext x
  simp [compression]

/-- Bosonic positive-defect endpoint rigidity. -/
theorem lower_endpoint_trace_rigidity (K : E →ₗ[ℝ] E) (U : Submodule ℝ E)
    (hK : (K-LinearMap.id).IsPositive)
    (ht : LinearMap.trace ℝ E K = LinearMap.trace ℝ U (compression K U) +
      (Module.finrank ℝ Uᗮ : ℝ)) :
    ∀ x ∈ Uᗮ, K x = x := by
  have hs := trace_eq_compression_add K U
  have hd : LinearMap.trace ℝ Uᗮ (compression (K-LinearMap.id) Uᗮ) = 0 := by
    rw [compression_sub, compression_id, map_sub, LinearMap.trace_id]
    linarith
  intro x hx
  have h := positive_compression_trace_zero hK Uᗮ hd x hx
  simpa only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using h

/-- Fermionic positive-defect endpoint rigidity, with the opposite defect sign. -/
theorem upper_endpoint_trace_rigidity (K : E →ₗ[ℝ] E) (U : Submodule ℝ E)
    (hK : (LinearMap.id-K).IsPositive)
    (ht : LinearMap.trace ℝ E K = LinearMap.trace ℝ U (compression K U) +
      (Module.finrank ℝ Uᗮ : ℝ)) :
    ∀ x ∈ Uᗮ, K x = x := by
  have hs := trace_eq_compression_add K U
  have hd : LinearMap.trace ℝ Uᗮ (compression (LinearMap.id-K) Uᗮ) = 0 := by
    rw [compression_sub, compression_id, map_sub, LinearMap.trace_id]
    linarith
  intro x hx
  have h := positive_compression_trace_zero hK Uᗮ hd x hx
  have h' : x-K x = 0 := h
  exact (sub_eq_zero.mp h').symm

/-- Endpoint identity kills actual cross blocks of the self-adjoint amplitude. -/
theorem cross_block_zero_of_endpoint (K : E →ₗ[ℝ] E) (hK : K.IsSymmetric)
    (U : Submodule ℝ E) (he : ∀ x ∈ Uᗮ, K x = x) :
    ∀ x ∈ Uᗮ, ∀ y ∈ U, ⟪K y,x⟫ = 0 := by
  intro x hx y hy
  rw [hK, he x hx]
  exact hx y hy
end Gaussian.Spectral
