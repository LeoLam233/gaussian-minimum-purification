import Gaussian.Phase.AuxiliaryOrbit

/-! Extend an identification of orthonormal coefficient frames to an ambient
orthogonal equivalence, with no complex structure or parity assumptions. -/
noncomputable section
namespace Gaussian.Phase
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Any two isometric coefficient frames of the same size differ by an
ambient orthogonal equivalence. The ambient complement may have any dimension. -/
theorem exists_orthogonal_extension (f g : F →ₗᵢ[ℝ] E) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x, R (g x) = f x := by
  obtain ⟨e,he⟩ := exists_range_isometry_of_inner_eq g.toLinearMap f.toLinearMap
    (fun x y => (g.inner_map_map x y).trans (f.inner_map_map x y).symm)
  let l : LinearMap.range g.toLinearMap →ₗᵢ[ℝ] E :=
    (LinearMap.range f.toLinearMap).subtypeₗᵢ.comp e.toLinearIsometry
  let R := l.extend
  refine ⟨LinearIsometryEquiv.ofSurjective R
    (LinearMap.surjective_of_injective R.injective),?_⟩
  intro x
  change l.extend (g x) = f x
  rw [l.extend_apply ⟨g x,LinearMap.mem_range_self g.toLinearMap x⟩]
  exact he x

end Gaussian.Phase
