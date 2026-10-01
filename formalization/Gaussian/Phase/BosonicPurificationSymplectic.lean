import Gaussian.Phase.BosonicPurificationDimension
import Gaussian.Phase.RawMetricOrbit

/-! Finite raw symplectic equivalences and extension machinery. Complement
identifications are constructed from proved skew adaptation and paired frames. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section RawForms
variable {D E : Type*} [AddCommGroup D] [Module ℝ D]
  [AddCommGroup E] [Module ℝ E]

/-- A form-preserving equivalence transports nondegeneracy. -/
theorem nondegenerate_of_form_equiv (σ : LinearMap.BilinForm ℝ D)
    (Ω : LinearMap.BilinForm ℝ E) (hσ : σ.Nondegenerate) (e : D ≃ₗ[ℝ] E)
    (he : ∀ x y, Ω (e x) (e y) = σ x y) : Ω.Nondegenerate := by
  constructor
  · intro x hx
    obtain ⟨y,rfl⟩ := e.surjective x
    have hy : y = 0 := hσ.1 y (fun z => (he y z).symm.trans (hx (e z)))
    simp [hy]
  · intro x hx
    obtain ⟨y,rfl⟩ := e.surjective x
    have hy : y = 0 := hσ.2 y (fun z => (he z y).symm.trans (hx (e z)))
    simp [hy]

/-- A symplectic frame is injective as a consequence of the nondegenerate
source form, not an additional rank hypothesis. -/
theorem symplectic_embedding_injective (σ : LinearMap.BilinForm ℝ D)
    (Ω : LinearMap.BilinForm ℝ E) (hσ : σ.Nondegenerate) (f : D →ₗ[ℝ] E)
    (hf : ∀ x y, Ω (f x) (f y) = σ x y) : Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hσ.1
  intro z
  rw [← hf]
  simp [map_sub,hxy]

/-- The actual range of a symplectic embedding has nondegenerate restricted form. -/
theorem symplectic_range_nondegenerate (σ : LinearMap.BilinForm ℝ D)
    (Ω : LinearMap.BilinForm ℝ E) (hσ : σ.Nondegenerate) (f : D →ₗ[ℝ] E)
    (hf : ∀ x y, Ω (f x) (f y) = σ x y) : (Ω.restrict (LinearMap.range f)).Nondegenerate := by
  let e := LinearEquiv.ofInjective f (symplectic_embedding_injective σ Ω hσ f hf)
  exact nondegenerate_of_form_equiv σ (Ω.restrict (LinearMap.range f)) hσ e hf

/-- A nondegenerate symplectic subspace has a genuine nondegenerate symplectic
complement and an actual direct-sum decomposition. -/
theorem symplectic_complement_data [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (P : Submodule ℝ E) (hP : (Ω.restrict P).Nondegenerate) :
    IsCompl P (Ω.orthogonal P) ∧ (Ω.restrict (Ω.orthogonal P)).Nondegenerate := by
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (B := Ω) hΩa.isRefl hP
  refine ⟨hc,?_⟩
  apply Ω.nondegenerate_restrict_of_disjoint_orthogonal hΩa.isRefl
  rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩa.isRefl P]
  exact hc.symm.disjoint

end RawForms

/-- Any two finite nondegenerate real alternating spaces of equal dimension
are symplectically equivalent. The equivalence is constructed through raw skew
adaptation and the previously proved complete paired-frame theorem. -/
theorem exists_symplectic_equiv_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Ω₁ : LinearMap.BilinForm ℝ E) (Ω₂ : LinearMap.BilinForm ℝ F)
    (ha₁ : Ω₁.IsAlt) (ha₂ : Ω₂.IsAlt) (hn₁ : Ω₁.Nondegenerate) (hn₂ : Ω₂.Nondegenerate)
    (hd : finrank ℝ E = finrank ℝ F) :
    ∃ e : E ≃ₗ[ℝ] F, ∀ x y, Ω₂ (e x) (e y) = Ω₁ x y := by
  let d₁ := bosonicAdaptationOfInner Ω₁ ha₁ hn₁
    (even_finrank_of_nondegenerate_alternating Ω₁ ha₁ hn₁)
  let d₂ := bosonicAdaptationOfInner Ω₂ ha₂ hn₂
    (even_finrank_of_nondegenerate_alternating Ω₂ ha₂ hn₂)
  obtain ⟨e,_,hJ,hg⟩ := exists_raw_metric_intertwiner d₁.g d₂.g
    d₁.metric_symm d₂.metric_symm d₁.metric_pos d₂.metric_pos d₁.J d₂.J
    d₁.square_neg d₂.square_neg d₁.metric_isometry d₂.metric_isometry
    (0 : ℝ →ₗ[ℝ] E) (0 : ℝ →ₗ[ℝ] F) hd (by intro x y; simp) (by intro x y; simp)
  refine ⟨e,?_⟩
  intro x y
  have h := hg x (d₁.J y)
  rw [hJ,d₂.metric_eq,d₁.metric_eq,d₂.square_neg,d₁.square_neg,map_neg,map_neg] at h
  exact neg_injective h

end Gaussian.Phase
