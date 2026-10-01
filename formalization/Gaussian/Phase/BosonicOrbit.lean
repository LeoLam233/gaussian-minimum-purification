import Gaussian.Phase.RawMetricOrbit

/-! Symplectic auxiliary orbits for two different positive compatible metrics.
All inputs are finite-dimensional raw real bilinear forms and linear maps;
no assertion about density operators or unitary implementers is included. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section CompatibleForms
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The covariance metric of a pure compatible complex structure is Ω(·,J·). -/
def compatibleMetric (Ω : LinearMap.BilinForm ℝ E) (J : E →ₗ[ℝ] E) :
    LinearMap.BilinForm ℝ E := Ω.compl₂ J

@[simp] theorem compatibleMetric_apply (Ω : LinearMap.BilinForm ℝ E)
    (J : E →ₗ[ℝ] E) (x y : E) : compatibleMetric Ω J x y = Ω x (J y) := rfl

/-- Alternation and symplectic compatibility force symmetry of ΩJ. -/
theorem compatibleMetric_symmetric (Ω : LinearMap.BilinForm ℝ E) (J : E →ₗ[ℝ] E)
    (hΩ : Ω.IsAlt) (hsq : ∀ x, J (J x) = -x)
    (hiso : ∀ x y, Ω (J x) (J y) = Ω x y) : (compatibleMetric Ω J).IsSymm := by
  constructor
  intro x y
  change Ω x (J y) = Ω y (J x)
  calc
    _ = Ω (J x) (J (J y)) := (hiso x (J y)).symm
    _ = -Ω (J x) y := by rw [hsq,map_neg]
    _ = _ := hΩ.neg_eq (J x) y

/-- The compatible metric is J-invariant. -/
theorem compatibleMetric_isometry (Ω : LinearMap.BilinForm ℝ E) (J : E →ₗ[ℝ] E)
    (hiso : ∀ x y, Ω (J x) (J y) = Ω x y) (x y : E) :
    compatibleMetric Ω J (J x) (J y) = compatibleMetric Ω J x y := hiso x (J y)

/-- Bosonic coefficient-level auxiliary orbit. The two compatible metrics may
be different everywhere outside the physical subspace. Equality on that
subspace suffices; no full-rank coupling or Euclidean orthogonality is assumed.
The conclusion preserves the original Ω, not a metric-dependent replacement. -/
theorem exists_symplectic_intertwiner_fixing_subspace [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt)
    (J₁ J₂ : E →ₗ[ℝ] E)
    (hJ₁sq : ∀ x, J₁ (J₁ x) = -x) (hJ₂sq : ∀ x, J₂ (J₂ x) = -x)
    (hJ₁Ω : ∀ x y, Ω (J₁ x) (J₁ y) = Ω x y)
    (hJ₂Ω : ∀ x y, Ω (J₂ x) (J₂ y) = Ω x y)
    (hp₁ : ∀ x, x ≠ 0 → 0 < Ω x (J₁ x))
    (hp₂ : ∀ x, x ≠ 0 → 0 < Ω x (J₂ x))
    (A : Submodule ℝ E)
    (hA : ∀ x ∈ A, ∀ y ∈ A, Ω x (J₁ y) = Ω x (J₂ y)) :
    ∃ R : E ≃ₗ[ℝ] E,
      (∀ x ∈ A, R x = x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) ∧
      (∀ x y, Ω (R x) (R y) = Ω x y) ∧
      (∀ x y, Ω (R x) (J₂ (R y)) = Ω x (J₁ y)) := by
  obtain ⟨R,hR,hRJ,hRg⟩ := exists_raw_metric_intertwiner
    (compatibleMetric Ω J₁) (compatibleMetric Ω J₂)
    (compatibleMetric_symmetric Ω J₁ hΩ hJ₁sq hJ₁Ω)
    (compatibleMetric_symmetric Ω J₂ hΩ hJ₂sq hJ₂Ω)
    hp₁ hp₂ J₁ J₂ hJ₁sq hJ₂sq
    (compatibleMetric_isometry Ω J₁ hJ₁Ω) (compatibleMetric_isometry Ω J₂ hJ₂Ω)
    A.subtype A.subtype rfl
    (fun x y => hA x x.property y y.property)
    (fun x y => (hJ₁Ω x y).trans (hJ₂Ω x y).symm)
  refine ⟨R,fun x hx => hR ⟨x,hx⟩,hRJ,?_,hRg⟩
  intro x y
  have hh := hRg x (J₁ y)
  change Ω (R x) (J₂ (R (J₁ y))) = Ω x (J₁ (J₁ y)) at hh
  rw [hRJ,hJ₂sq,hJ₁sq,map_neg,map_neg] at hh
  exact neg_injective hh


/-- A positive compatible metric forces nondegeneracy of the original Ω. -/
theorem nondegenerate_of_compatible_positive (Ω : LinearMap.BilinForm ℝ E)
    (hΩ : Ω.IsAlt) (J : E →ₗ[ℝ] E)
    (hp : ∀ x, x ≠ 0 → 0 < Ω x (J x)) : Ω.Nondegenerate := by
  constructor
  · intro x hx
    by_contra hn
    have ht := hp x hn
    rw [hx (J x)] at ht
    exact (lt_irrefl 0) ht
  · intro x hx
    by_contra hn
    have hz : Ω x (J x) = 0 := hΩ.isRefl (J x) x (hx (J x))
    have ht := hp x hn
    rw [hz] at ht
    exact (lt_irrefl 0) ht

/-- Restrict a physical-pointwise-fixing symplectic map to the actual Ω
orthogonal auxiliary subspace. The result is surjective, including in dimension zero. -/
def symplecticAuxiliaryRestriction [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (A : Submodule ℝ E) (R : E ≃ₗ[ℝ] E)
    (hR : ∀ x ∈ A, R x = x) (hΩR : ∀ x y, Ω (R x) (R y) = Ω x y) :
    Ω.orthogonal A ≃ₗ[ℝ] Ω.orthogonal A := by
  have hm : ∀ x ∈ Ω.orthogonal A, R x ∈ Ω.orthogonal A := by
    intro x hx a ha
    calc
      Ω a (R x) = Ω (R a) (R x) := by rw [hR a ha]
      _ = Ω a x := hΩR a x
      _ = 0 := hx a ha
  let l := R.toLinearMap.restrict hm
  have hi : Function.Injective l := by
    intro x y hxy
    apply Subtype.ext
    exact R.injective (congrArg Subtype.val hxy)
  exact LinearEquiv.ofBijective l ⟨hi,LinearMap.surjective_of_injective hi⟩

@[simp] theorem symplecticAuxiliaryRestriction_apply [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (A : Submodule ℝ E) (R : E ≃ₗ[ℝ] E)
    (hR : ∀ x ∈ A, R x = x) (hΩR : ∀ x y, Ω (R x) (R y) = Ω x y)
    (x : Ω.orthogonal A) : (symplecticAuxiliaryRestriction Ω A R hR hΩR x : E) = R x := rfl

/-- Sector-correct auxiliary block form for a nondegenerate physical symplectic
subspace. The complement here is Ω-orthogonal, never a chosen Euclidean complement. -/
theorem symplectic_auxiliary_block [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (R : E ≃ₗ[ℝ] E) (hR : ∀ x ∈ A, R x = x)
    (hΩR : ∀ x y, Ω (R x) (R y) = Ω x y) :
    IsCompl A (Ω.orthogonal A) ∧ (Ω.restrict (Ω.orthogonal A)).Nondegenerate ∧
    ∃ Q : Ω.orthogonal A ≃ₗ[ℝ] Ω.orthogonal A,
      (∀ x y, Ω (Q x) (Q y) = Ω x y) ∧
      (∀ (a : A) (c : Ω.orthogonal A), R ((a : E)+(c : E)) = (a : E)+(Q c : E)) := by
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (B := Ω) hΩ.isRefl hA
  have hn : (Ω.restrict (Ω.orthogonal A)).Nondegenerate := by
    apply Ω.nondegenerate_restrict_of_disjoint_orthogonal hΩ.isRefl
    rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩ.isRefl A]
    exact hc.symm.disjoint
  refine ⟨hc,hn,symplecticAuxiliaryRestriction Ω A R hR hΩR,?_,?_⟩
  · intro x y
    simpa only [symplecticAuxiliaryRestriction_apply] using hΩR x y
  · intro a c
    rw [map_add,hR a a.property,symplecticAuxiliaryRestriction_apply]


/-- Complete raw bosonic auxiliary-orbit statement on a physical symplectic
subspace and its true Ω-orthogonal auxiliary complement. -/
theorem exists_symplectic_auxiliary_orbit [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt)
    (J₁ J₂ : E →ₗ[ℝ] E)
    (hJ₁sq : ∀ x, J₁ (J₁ x) = -x) (hJ₂sq : ∀ x, J₂ (J₂ x) = -x)
    (hJ₁Ω : ∀ x y, Ω (J₁ x) (J₁ y) = Ω x y)
    (hJ₂Ω : ∀ x y, Ω (J₂ x) (J₂ y) = Ω x y)
    (hp₁ : ∀ x, x ≠ 0 → 0 < Ω x (J₁ x))
    (hp₂ : ∀ x, x ≠ 0 → 0 < Ω x (J₂ x))
    (A : Submodule ℝ E) (hAn : (Ω.restrict A).Nondegenerate)
    (hA : ∀ x ∈ A, ∀ y ∈ A, Ω x (J₁ y) = Ω x (J₂ y)) :
    IsCompl A (Ω.orthogonal A) ∧ (Ω.restrict (Ω.orthogonal A)).Nondegenerate ∧
    ∃ (R : E ≃ₗ[ℝ] E) (Q : Ω.orthogonal A ≃ₗ[ℝ] Ω.orthogonal A),
      (∀ x ∈ A, R x = x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) ∧
      (∀ x y, Ω (R x) (R y) = Ω x y) ∧
      (∀ x y, Ω (Q x) (Q y) = Ω x y) ∧
      (∀ (a : A) (c : Ω.orthogonal A), R ((a : E)+(c : E)) = (a : E)+(Q c : E)) := by
  obtain ⟨R,hR,hRJ,hRΩ,_⟩ := exists_symplectic_intertwiner_fixing_subspace
    Ω hΩ J₁ J₂ hJ₁sq hJ₂sq hJ₁Ω hJ₂Ω hp₁ hp₂ A hA
  obtain ⟨hc,hn,Q,hQΩ,hQ⟩ := symplectic_auxiliary_block Ω hΩ
    (nondegenerate_of_compatible_positive Ω hΩ J₁ hp₁) A hAn R hR hRΩ
  exact ⟨hc,hn,R,Q,hR,hRJ,hRΩ,hQΩ,hQ⟩

end CompatibleForms
end Gaussian.Phase
