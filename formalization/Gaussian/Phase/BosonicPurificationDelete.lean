import Gaussian.Phase.BosonicPurificationRestriction

/-! Actual covariance-only restriction and pure-factor deletion. The smaller
pure covariance and its protected physical embedding are constructed explicitly. -/
noncomputable section
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {Ω : LinearMap.BilinForm ℝ E} (d : PureCompatibleCovariance Ω)

/-- Restrict an actual pure covariance to an invariant coefficient subspace. -/
def restrict (P : Submodule ℝ E) (hP : ∀ x ∈ P, d.generator x ∈ P) :
    PureCompatibleCovariance (Ω.restrict P) where
  form := d.form.restrict P
  generator := d.generator.restrict hP
  symmetric := ⟨fun x y => d.symmetric.eq x y⟩
  positive x hx := d.positive x (by
    intro h
    apply hx
    exact Subtype.ext h)
  square_neg x := by apply Subtype.ext; exact d.square_neg x
  compatible x y := d.compatible x y
  symplectic x y := d.symplectic x y

@[simp] theorem restrict_form (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, d.generator x ∈ P) (x y : P) :
    (d.restrict P hP).form x y = d.form x y := rfl

@[simp] theorem restrict_generator (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, d.generator x ∈ P) (x : P) :
    ((d.restrict P hP).generator x : E) = d.generator x := rfl

/-- Delete a genuinely pure restricted factor. Ambient invariance of its
complement is derived from the local square/compatibility equations. -/
def deletePureSubspace [FiniteDimensional ℝ E] (P : Submodule ℝ E)
    (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) :
    PureCompatibleCovariance (Ω.restrict (Ω.orthogonal P)) :=
  d.restrict (Ω.orthogonal P) (d.pure_restriction_split P Jp hsq hcompat).2.1

@[simp] theorem deletePureSubspace_form [FiniteDimensional ℝ E] (P : Submodule ℝ E)
    (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) (x y : Ω.orthogonal P) :
    (d.deletePureSubspace P Jp hsq hcompat).form x y = d.form x y := rfl

end PureCompatibleCovariance

/-- An auxiliary symplectic factor leaves the protected physical space inside
the retained complement, giving a concrete post-deletion embedding. -/
def retainedPhysicalEmbedding {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) (A P : Submodule ℝ E)
    (hPA : P ≤ Ω.orthogonal A) : A →ₗ[ℝ] Ω.orthogonal P :=
  A.subtype.codRestrict (Ω.orthogonal P) (fun a p hp =>
    hΩ.isRefl a p (hPA hp a a.property))

@[simp] theorem retainedPhysicalEmbedding_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) (A P : Submodule ℝ E)
    (hPA : P ≤ Ω.orthogonal A) (a : A) :
    (retainedPhysicalEmbedding Ω hΩ A P hPA a : E) = a := rfl

/-- The deleted pure covariance restricts to exactly the original physical
covariance and commutator along the constructed retained embedding. -/
theorem deletePureSubspace_physical {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {Ω : LinearMap.BilinForm ℝ E} (hΩ : Ω.IsAlt)
    (d : PureCompatibleCovariance Ω) (A P : Submodule ℝ E)
    (hPA : P ≤ Ω.orthogonal A) (Jp : P →ₗ[ℝ] P) (hsq : ∀ x, Jp (Jp x) = -x)
    (hcompat : ∀ x y : P, d.form x y = Ω x (Jp y)) (x y : A) :
    (d.deletePureSubspace P Jp hsq hcompat).form
        (retainedPhysicalEmbedding Ω hΩ A P hPA x) (retainedPhysicalEmbedding Ω hΩ A P hPA y) =
      d.form x y ∧
    (Ω.restrict (Ω.orthogonal P))
        (retainedPhysicalEmbedding Ω hΩ A P hPA x) (retainedPhysicalEmbedding Ω hΩ A P hPA y) =
      Ω x y := ⟨rfl,rfl⟩

end Gaussian.Phase
