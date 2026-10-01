import Gaussian.Phase.Restriction

/-! Purity of an actual compressed orthogonal covariance forces the selected
subspace to decouple. No global invariance is assumed. -/
noncomputable section
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual orthogonal compression preserves skew-adjointness. -/
theorem compression_isSkew (T : E →ₗ[ℝ] E) (hT : IsSkew T) (P : Submodule ℝ E) :
    IsSkew (compression T P) := by
  intro x y
  change ⟪P.orthogonalProjectionOnto (T x),y⟫ = -⟪x,P.orthogonalProjectionOnto (T y)⟫
  rw [P.inner_orthogonalProjectionOnto_eq_of_mem_right,
    P.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT x y

/-- A skew square root of minus identity preserves norms. -/
theorem norm_eq_of_skew_square_neg (T : E →ₗ[ℝ] E) (hT : IsSkew T)
    (hsq : ∀ x, T (T x) = -x) (x : E) : ‖T x‖ = ‖x‖ := by
  have h : ⟪T x,T x⟫ = ⟪x,x⟫ := by rw [hT,hsq,inner_neg_right,neg_neg]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

namespace OrthogonalComplexStructure
/-- If the actual compressed generator is pure, the selected subspace is
already invariant under the global generator. This includes zero subspaces. -/
theorem invariant_of_pure_compression (J : OrthogonalComplexStructure E)
    (P : Submodule ℝ E)
    (hPure : ∀ x : P, compression J.linear P (compression J.linear P x) = -x) :
    J.IsInvariant P := by
  intro x hx
  apply (P.mem_iff_norm_starProjection (J x)).mpr
  have h := norm_eq_of_skew_square_neg (compression J.linear P)
    (compression_isSkew J.linear J.inner_map_left P) hPure ⟨x,hx⟩
  change ‖P.starProjection (J x)‖ = ‖x‖ at h
  rw [J.equiv.norm_map]
  exact h

/-- Both sides of a pure compressed cut are globally invariant. -/
theorem invariant_split_of_pure_compression (J : OrthogonalComplexStructure E)
    (P : Submodule ℝ E)
    (hPure : ∀ x : P, compression J.linear P (compression J.linear P x) = -x) :
    J.IsInvariant P ∧ J.IsInvariant Pᗮ := by
  have h := J.invariant_of_pure_compression P hPure
  exact ⟨h,J.orthogonal_invariant h⟩

/-- Operator-equation version for covariance-purity interfaces. -/
theorem invariant_of_compression_square (J : OrthogonalComplexStructure E)
    (P : Submodule ℝ E)
    (hPure : compression J.linear P * compression J.linear P = -LinearMap.id) :
    J.IsInvariant P ∧ J.IsInvariant Pᗮ :=
  J.invariant_split_of_pure_compression P (fun x => LinearMap.congr_fun hPure x)

end OrthogonalComplexStructure
end Gaussian.Phase
