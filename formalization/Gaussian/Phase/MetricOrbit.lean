import Gaussian.Phase.AuxiliaryOrbit

/-! The orthogonal orbit argument with two genuinely different ambient metrics.
The physical data enter through two linear embeddings with equal metric and
skew Gram forms. No metric is shared between the ambient spaces. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace OrthogonalComplexStructure
variable {D E F : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Synthesis from an arbitrary common coefficient domain. -/
def embeddedHullMap (J : OrthogonalComplexStructure E) (ι : D →ₗ[ℝ] E) : D × D →ₗ[ℝ] E :=
  ι.coprod (J.linear.comp ι)

@[simp] theorem embeddedHullMap_apply (J : OrthogonalComplexStructure E)
    (ι : D →ₗ[ℝ] E) (x : D × D) : J.embeddedHullMap ι x = ι x.1 + J (ι x.2) := rfl

theorem embeddedHull_invariant (J : OrthogonalComplexStructure E) (ι : D →ₗ[ℝ] E) :
    J.IsInvariant (LinearMap.range (J.embeddedHullMap ι)) := by
  rintro x ⟨⟨a,b⟩,rfl⟩
  refine ⟨(-b,a),?_⟩
  simp [add_comm]

/-- Both Gram forms suffice to identify the full synthesized hull. -/
theorem embeddedHull_inner_eq (J₁ : OrthogonalComplexStructure E)
    (J₂ : OrthogonalComplexStructure F) (ι₁ : D →ₗ[ℝ] E) (ι₂ : D →ₗ[ℝ] F)
    (hg : ∀ x y, ⟪ι₁ x,ι₁ y⟫ = ⟪ι₂ x,ι₂ y⟫)
    (hJ : ∀ x y, ⟪J₁ (ι₁ x),ι₁ y⟫ = ⟪J₂ (ι₂ x),ι₂ y⟫) (x y : D × D) :
    ⟪J₁.embeddedHullMap ι₁ x,J₁.embeddedHullMap ι₁ y⟫ =
      ⟪J₂.embeddedHullMap ι₂ x,J₂.embeddedHullMap ι₂ y⟫ := by
  simp only [embeddedHullMap_apply,inner_add_left,inner_add_right,
    J₁.inner_map_map,J₂.inner_map_map,hg,hJ]
  have hh : ⟪ι₁ x.1,J₁ (ι₁ y.2)⟫ = ⟪ι₂ x.1,J₂ (ι₂ y.2)⟫ := by
    calc
      _ = ⟪J₁ (ι₁ y.2),ι₁ x.1⟫ := real_inner_comm _ _
      _ = ⟪J₂ (ι₂ y.2),ι₂ x.1⟫ := hJ y.2 x.1
      _ = _ := real_inner_comm _ _
  rw [hh]

/-- Glue maps between orthogonal decompositions in different metric spaces. -/
def glueOrthogonalBetween [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (P : Submodule ℝ E) (Q : Submodule ℝ F)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) : E ≃ₗᵢ[ℝ] F :=
  (P.orthogonalDecomposition.trans (e.withLpProdCongr 2 f)).trans
    Q.orthogonalDecomposition.symm

theorem glueOrthogonalBetween_apply_add [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (P : Submodule ℝ E) (Q : Submodule ℝ F)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) (x : P) (y : Pᗮ) :
    glueOrthogonalBetween P Q e f ((x : E)+(y : E)) = (e x : F)+(f y : F) := by
  have hs : (x : E)+(y : E) = P.orthogonalDecomposition.symm (.toLp 2 (x,y)) := by simp
  rw [hs]
  change Q.orthogonalDecomposition.symm ((e.withLpProdCongr 2 f)
    (P.orthogonalDecomposition (P.orthogonalDecomposition.symm (.toLp 2 (x,y))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Two equal-dimensional pure coefficient spaces with identical physical
metric and skew Gram forms admit an intertwining isometry extending the
physical identification. Degenerate embeddings are allowed as well. -/
theorem exists_intertwiner_of_embedding_grams
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (J₁ : OrthogonalComplexStructure E) (J₂ : OrthogonalComplexStructure F)
    (ι₁ : D →ₗ[ℝ] E) (ι₂ : D →ₗ[ℝ] F) (hd : finrank ℝ E = finrank ℝ F)
    (hg : ∀ x y, ⟪ι₁ x,ι₁ y⟫ = ⟪ι₂ x,ι₂ y⟫)
    (hJ : ∀ x y, ⟪J₁ (ι₁ x),ι₁ y⟫ = ⟪J₂ (ι₂ x),ι₂ y⟫) :
    ∃ R : E ≃ₗᵢ[ℝ] F,
      (∀ x, R (ι₁ x) = ι₂ x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) := by
  let P := LinearMap.range (J₁.embeddedHullMap ι₁)
  let Q := LinearMap.range (J₂.embeddedHullMap ι₂)
  have hP : J₁.IsInvariant P := J₁.embeddedHull_invariant ι₁
  have hQ : J₂.IsInvariant Q := J₂.embeddedHull_invariant ι₂
  have hP' := J₁.orthogonal_invariant hP
  have hQ' := J₂.orthogonal_invariant hQ
  obtain ⟨e,he⟩ := exists_range_isometry_of_inner_eq
    (J₁.embeddedHullMap ι₁) (J₂.embeddedHullMap ι₂)
    (J₁.embeddedHull_inner_eq J₂ ι₁ ι₂ hg hJ)
  have heJ (x : P) : (e ⟨J₁ x,hP x x.property⟩ : F) = J₂ (e x) := by
    rcases x with ⟨x,⟨⟨a,b⟩,rfl⟩⟩
    have hs : J₁ (J₁.embeddedHullMap ι₁ (a,b)) = J₁.embeddedHullMap ι₁ (-b,a) := by
      simp [add_comm]
    simp only [hs]
    erw [he (-b,a),he (a,b)]
    simp [add_comm]
  have hd' : finrank ℝ Pᗮ = finrank ℝ Qᗮ := by
    have hedim := e.toLinearEquiv.finrank_eq
    have hpd := P.finrank_add_finrank_orthogonal
    have hqd := Q.finrank_add_finrank_orthogonal
    change finrank ℝ P = finrank ℝ Q at hedim
    omega
  obtain ⟨f,hfJ⟩ := (J₁.restrict Pᗮ hP').exists_intertwiner_of_finrank_eq
    (J₂.restrict Qᗮ hQ') hd'
  let R := glueOrthogonalBetween P Q e f
  have hRl (x : P) : R x = (e x : F) := by
    simpa using glueOrthogonalBetween_apply_add P Q e f x 0
  have hRr (x : Pᗮ) : R x = (f x : F) := by
    simpa using glueOrthogonalBetween_apply_add P Q e f 0 x
  refine ⟨R,?_,?_⟩
  · intro x
    have hx : ι₁ x ∈ P := ⟨(x,0),by simp⟩
    rw [hRl ⟨ι₁ x,hx⟩]
    convert he (x,0) using 1 <;> simp
  · intro x
    have hl (p : P) : R (J₁ p) = J₂ (R p) := by
      calc
        _ = (e ⟨J₁ p,hP p p.property⟩ : F) := hRl _
        _ = J₂ (e p) := heJ p
        _ = _ := congrArg J₂ (hRl p).symm
    have hr (q : Pᗮ) : R (J₁ q) = J₂ (R q) := by
      calc
        _ = (f (J₁.restrict Pᗮ hP' q) : F) := hRr _
        _ = (J₂.restrict Qᗮ hQ' (f q) : F) := congrArg Subtype.val (hfJ q)
        _ = _ := congrArg J₂ (hRr q).symm
    let p := P.orthogonalProjectionOnto x
    let q := Pᗮ.orthogonalProjectionOnto x
    have hx : (p : E)+(q : E) = x := P.starProjection_add_starProjection_orthogonal x
    rw [← hx,J₁.apply_add,map_add,hl,hr,← J₂.apply_add,← map_add]

end OrthogonalComplexStructure
end Gaussian.Phase
