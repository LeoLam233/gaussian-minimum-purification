import Gaussian.Phase.MetricOrbit

noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

/-- Raw-form version of the two-metric orbit theorem. The ambient vector spaces
may later be identified, while their norm and inner-product instances remain
independent throughout this proof. -/
theorem exists_raw_metric_intertwiner
    {D E F : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (g₁ : LinearMap.BilinForm ℝ E) (g₂ : LinearMap.BilinForm ℝ F)
    (hg₁s : g₁.IsSymm) (hg₂s : g₂.IsSymm)
    (hg₁p : ∀ x, x ≠ 0 → 0 < g₁ x x) (hg₂p : ∀ x, x ≠ 0 → 0 < g₂ x x)
    (J₁ : E →ₗ[ℝ] E) (J₂ : F →ₗ[ℝ] F)
    (hJ₁sq : ∀ x, J₁ (J₁ x) = -x) (hJ₂sq : ∀ x, J₂ (J₂ x) = -x)
    (hJ₁g : ∀ x y, g₁ (J₁ x) (J₁ y) = g₁ x y)
    (hJ₂g : ∀ x y, g₂ (J₂ x) (J₂ y) = g₂ x y)
    (ι₁ : D →ₗ[ℝ] E) (ι₂ : D →ₗ[ℝ] F) (hd : finrank ℝ E = finrank ℝ F)
    (hg : ∀ x y, g₁ (ι₁ x) (ι₁ y) = g₂ (ι₂ x) (ι₂ y))
    (hJ : ∀ x y, g₁ (J₁ (ι₁ x)) (ι₁ y) = g₂ (J₂ (ι₂ x)) (ι₂ y)) :
    ∃ R : E ≃ₗ[ℝ] F,
      (∀ x, R (ι₁ x) = ι₂ x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) ∧
      (∀ x y, g₂ (R x) (R y) = g₁ x y) := by
  let core₁ := covarianceInnerCore g₁ hg₁s hg₁p
  let core₂ := covarianceInnerCore g₂ hg₂s hg₂p
  letI : NormedAddCommGroup E := core₁.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore core₁.toCore
  letI : NormedAddCommGroup F := core₂.toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore core₂.toCore
  let C₁ : OrthogonalComplexStructure E :=
    { equiv := LinearIsometryEquiv.ofSurjective
        { toLinearMap := J₁
          norm_map' := fun x => by
            rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
              ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
            exact hJ₁g x x }
        (fun x => ⟨-J₁ x,by change J₁ (-J₁ x) = x; simp [hJ₁sq]⟩)
      square_neg := hJ₁sq }
  let C₂ : OrthogonalComplexStructure F :=
    { equiv := LinearIsometryEquiv.ofSurjective
        { toLinearMap := J₂
          norm_map' := fun x => by
            rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
              ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
            exact hJ₂g x x }
        (fun x => ⟨-J₂ x,by change J₂ (-J₂ x) = x; simp [hJ₂sq]⟩)
      square_neg := hJ₂sq }
  obtain ⟨R,hR,hRJ⟩ := C₁.exists_intertwiner_of_embedding_grams C₂ ι₁ ι₂ hd hg hJ
  exact ⟨R.toLinearEquiv,hR,hRJ,R.inner_map_map⟩


end Gaussian.Phase
