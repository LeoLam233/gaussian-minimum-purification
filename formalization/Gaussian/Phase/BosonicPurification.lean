import Gaussian.Phase.BosonicPurificationOpposite
import Gaussian.Phase.BosonicPurificationOrientation
import Gaussian.Phase.BosonicPurificationDimension

/-! A covariance-only reference purification for every finite admissible
bosonic pair. The auxiliary orientation is converted explicitly, yielding
Ω⊕Ω and an exact physical restriction. No state or entropy conclusion is made. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

/-- Nondegeneracy of a raw direct-sum commutator is proved componentwise. -/
theorem doubledForm_nondegenerate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B₁ B₂ : LinearMap.BilinForm ℝ E) (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate) :
    (doubledForm B₁ B₂).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply h₁.1
      intro y
      simpa using hx (y,0)
    · apply h₂.1
      intro y
      simpa using hx (0,y)
  · intro x hx
    apply Prod.ext
    · apply h₁.2
      intro y
      simpa using hx (y,0)
    · apply h₂.2
      intro y
      simpa using hx (0,y)

namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- Act identically on the physical copy and reverse only the actual paired
auxiliary orientation. -/
def auxiliaryOrientation : (E × E) ≃ₗ[ℝ] (E × E) :=
  (LinearEquiv.refl ℝ E).prodCongr b.reflection.toLinearEquiv

@[simp] theorem auxiliaryOrientation_apply (x : E × E) :
    b.auxiliaryOrientation x = (x.1,b.reflection x.2) := rfl

/-- The opposite auxiliary form becomes the same-sign original form by an
actual proved coordinate transformation. -/
theorem auxiliaryOrientation_commutator :
    (doubledForm J.symplecticForm (-J.symplecticForm)).compl₁₂
      b.auxiliaryOrientation.toLinearMap b.auxiliaryOrientation.toLinearMap =
      doubledForm J.symplecticForm J.symplecticForm := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change J.symplecticForm x.1 y.1 - J.symplecticForm (b.reflection x.2) (b.reflection y.2) =
    J.symplecticForm x.1 y.1 + J.symplecticForm x.2 y.2
  rw [b.reflection_antisymplectic,sub_neg_eq_add]

/-- The same-sign doubled pure covariance, after the explicit auxiliary
orientation conversion. -/
def pureSame (hν : ∀ i, 1 ≤ b.value i) :
    PureCompatibleCovariance (doubledForm J.symplecticForm J.symplecticForm) :=
  ((b.pureOpposite hν).pullback b.auxiliaryOrientation).of_form_eq
    b.auxiliaryOrientation_commutator

/-- The orientation conversion leaves the exact physical covariance unchanged. -/
theorem pureSame_physical (hν : ∀ i, 1 ≤ b.value i) (x y : E) :
    (b.pureSame hν).form (x,0) (y,0) = ⟪x,K y⟫ := by
  simp [pureSame,b.pureOpposite_physical]

end PairedEigenframe

section RawReference
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Construct a same-sign reference purifier from the checked raw Williamson
frame. Strict positivity is derived from uncertainty and nondegeneracy. -/
theorem exists_bosonic_reference_of_mode_count
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate) {n : ℕ} (hn : finrank ℝ E = 2*n)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) :
    ∃ p : PureCompatibleCovariance (doubledForm Ω Ω),
      (∀ x y, p.form (x,0) (y,0) = V x y) ∧
      Gaussian.Covariance.RealifiedUncertainty p.form (doubledForm Ω Ω) := by
  obtain ⟨d,hLower⟩ := Gaussian.Covariance.exists_bosonicAdaptation_from_uncertainty
    V Ω hV hΩa hΩn (by refine ⟨n,?_⟩; omega) hUnc
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  let b := d.pairedFrame hn
  have hν : ∀ i, 1 ≤ b.value i := d.pairedFrame_value_ge_one hLower hn
  let q := b.pureSame hν
  have hΩ : doubledForm d.complexStructure.symplecticForm d.complexStructure.symplecticForm =
      doubledForm Ω Ω := by rw [d.complexStructure_symplecticForm]
  let p := q.of_form_eq hΩ
  refine ⟨p,?_,p.uncertainty⟩
  intro x y
  change (q.of_form_eq hΩ).form (x,0) (y,0) = V x y
  rw [PureCompatibleCovariance.of_form_eq_form]
  change (b.pureSame hν).form (x,0) (y,0) = V x y
  rw [b.pureSame_physical]
  exact (d.covariance_factor x y).symm

/-- Every finite admissible bosonic covariance has a doubled same-sign pure
compatible covariance. No supplied mode count, invertible mixed defect, or
positive squeezing parameter is required. -/
theorem exists_bosonic_reference_compatible
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) :
    ∃ p : PureCompatibleCovariance (doubledForm Ω Ω),
      (∀ x y, p.form (x,0) (y,0) = V x y) ∧
      Gaussian.Covariance.RealifiedUncertainty p.form (doubledForm Ω Ω) := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  exact exists_bosonic_reference_of_mode_count V Ω hV hΩa hΩn (n := n) (by omega) hUnc

/-- Expanded covariance-only reference purification theorem. The doubled
commutator is literally Ω⊕Ω, its physical restriction is literally Ω, and the
positive covariance restricts literally to V. Purity is the proved generator
square identity and compatible-metric relation, without a state interpretation. -/
theorem exists_bosonic_reference_purification
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) :
    ∃ (W : LinearMap.BilinForm ℝ (E × E)) (Jp : (E × E) →ₗ[ℝ] (E × E)),
      W.IsSymm ∧ (∀ z, z ≠ 0 → 0 < W z z) ∧
      (∀ z, Jp (Jp z) = -z) ∧
      (∀ z w, W z w = doubledForm Ω Ω z (Jp w)) ∧
      (∀ z w, doubledForm Ω Ω (Jp z) (Jp w) = doubledForm Ω Ω z w) ∧
      (doubledForm Ω Ω).IsAlt ∧ (doubledForm Ω Ω).Nondegenerate ∧
      Gaussian.Covariance.RealifiedUncertainty W (doubledForm Ω Ω) ∧
      (∀ x y, W (x,0) (y,0) = V x y) ∧
      (∀ x y, doubledForm Ω Ω (x,0) (y,0) = Ω x y) := by
  obtain ⟨p,hp,hunc⟩ := exists_bosonic_reference_compatible V Ω hV hΩa hΩn hUnc
  exact ⟨p.form,p.generator,p.symmetric,p.positive,p.square_neg,p.compatible,p.symplectic,
    doubledForm_alternating Ω Ω hΩa hΩa,doubledForm_nondegenerate Ω Ω hΩn hΩn,
    hunc,hp,doubledForm_physical Ω Ω⟩

end RawReference
end Gaussian.Phase
