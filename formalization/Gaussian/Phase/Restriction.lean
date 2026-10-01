import Gaussian.Phase.BosonicAdaptation
import Gaussian.Spectral.Interlacing

/-! Genuine restricted forms and their generators on invariant coefficient
subspaces. The compression is the actual orthogonal projection, never a spectral
interface field. Density states and entropy identification are separate results. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Phase

section InnerGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace OrthogonalComplexStructure
variable (J : OrthogonalComplexStructure E) (U : Submodule ℝ E) (hU : J.IsInvariant U)
include hU

/-- Restriction of an orthogonal complex structure to an invariant real subspace. -/
def restrict : OrthogonalComplexStructure U where
  equiv := LinearIsometryEquiv.ofSurjective
    { toLinearMap := J.linear.restrict hU
      norm_map' := fun x => J.equiv.norm_map x }
    (fun x => ⟨⟨-J x,U.neg_mem (hU x x.property)⟩,by
      apply Subtype.ext
      change J (-J x) = (x : E)
      simp⟩)
  square_neg x := by apply Subtype.ext; exact J.square_neg x

@[simp] theorem restrict_apply (x : U) : (J.restrict U hU x : E) = J x := rfl

/-- Projection commutes with J precisely because the retained subspace is invariant. -/
theorem restrict_projection (x : E) :
    J.restrict U hU (U.orthogonalProjectionOnto x) = U.orthogonalProjectionOnto (J x) := by
  apply ext_inner_left ℝ
  intro y
  calc
    ⟪y,J.restrict U hU (U.orthogonalProjectionOnto x)⟫ =
        -⟪J.restrict U hU y,U.orthogonalProjectionOnto x⟫ := by
      linarith [(J.restrict U hU).inner_map_left y (U.orthogonalProjectionOnto x)]
    _ = -⟪J y,x⟫ := congrArg Neg.neg
      (U.inner_orthogonalProjectionOnto_eq_of_mem_left (J.restrict U hU y) x)
    _ = ⟪(y : E),J x⟫ := by rw [J.inner_map_left,neg_neg]
    _ = ⟪y,U.orthogonalProjectionOnto (J x)⟫ :=
      (U.inner_orthogonalProjectionOnto_eq_of_mem_left y (J x)).symm

/-- Compression of J K factors through the restricted J and the actual K compression. -/
theorem compression_factor {T K : E →ₗ[ℝ] E} (hT : ∀ x, T x = J (K x)) (x : U) :
    compression T U x = J.restrict U hU (compression K U x) := by
  change U.orthogonalProjectionOnto (T x) =
    J.restrict U hU (U.orthogonalProjectionOnto (K x))
  rw [hT,J.restrict_projection U hU]

/-- Commutation descends to a genuine compression; K-invariance of U is not assumed. -/
theorem compression_commute (K : E →ₗ[ℝ] E) (hK : ∀ x, J (K x) = K (J x)) (x : U) :
    J.restrict U hU (compression K U x) = compression K U (J.restrict U hU x) := by
  change J.restrict U hU (U.orthogonalProjectionOnto (K x)) =
    U.orthogonalProjectionOnto (K (J x))
  rw [J.restrict_projection U hU,hK]

/-- The square identity for the actual compressed skew generator. -/
theorem compression_neg_square {T K : E →ₗ[ℝ] E}
    (hT : ∀ x, T x = J (K x)) (hK : ∀ x, J (K x) = K (J x)) :
    -(compression T U * compression T U) = compression K U * compression K U := by
  apply LinearMap.ext
  intro x
  change -compression T U (compression T U x) = compression K U (compression K U x)
  rw [J.compression_factor U hU hT,J.compression_factor U hU hT,
    ← J.compression_commute U hU K hK,(J.restrict U hU).square_neg,neg_neg]

end OrthogonalComplexStructure

/-- The real skew bilinear covariance associated with an operator. -/
def skewCovarianceForm (T : E →ₗ[ℝ] E) : LinearMap.BilinForm ℝ E :=
  (innerₗ E).compl₂ T

/-- The generator of the genuinely restricted skew covariance equals the
Euclidean compression, proved by its independent duality characterization. -/
theorem restricted_skew_generator (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) :
    formGenerator ((skewCovarianceForm T).restrict U) = compression T U := by
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [inner_formGenerator,inner_compression]
  rfl

/-- C3-F: the actual restricted covariance generator factors as J_U K_U. -/
theorem fermionic_restricted_factor {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (U : Submodule ℝ E) (hU : d.complexStructure.IsInvariant U) (x : U) :
    formGenerator ((skewCovarianceForm T).restrict U) x =
      d.complexStructure.restrict U hU (compression d.K U x) := by
  rw [restricted_skew_generator]
  exact d.complexStructure.compression_factor U hU d.factor x

/-- C3-F: the square of the actual restricted covariance determines K_U². -/
theorem fermionic_restricted_neg_square {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (U : Submodule ℝ E) (hU : d.complexStructure.IsInvariant U) :
    -(formGenerator ((skewCovarianceForm T).restrict U) *
        formGenerator ((skewCovarianceForm T).restrict U)) =
      compression d.K U * compression d.K U := by
  rw [restricted_skew_generator]
  exact d.complexStructure.compression_neg_square U hU d.factor d.commute

end InnerGeometry
section GeneralizedGenerators
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Left-slot generalized generator: Ω(Gx,y)=V(x,y).
Convention correction: this is −JK when g=ΩJ and V=gK. It is not the
right-slot matrix operator Ω_matrix⁻¹ V_matrix. -/
def leftFormGenerator (V Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.Nondegenerate) : E →ₗ[ℝ] E :=
  (LinearMap.BilinForm.toDual Ω hΩ).symm.toLinearMap ∘ₗ V

@[simp] theorem leftFormGenerator_pairing (V Ω : LinearMap.BilinForm ℝ E)
    (hΩ : Ω.Nondegenerate) (x y : E) : Ω (leftFormGenerator V Ω hΩ x) y = V x y := by
  exact congrArg (fun f : Module.Dual ℝ E => f y)
    ((LinearMap.BilinForm.toDual Ω hΩ).apply_symm_apply (V x))

/-- Right-slot generalized generator: Ω(x,Gy)=V(x,y).
Under the manuscript's convention g=ΩJ, this is +JK and is the literal
matrix operator Ω_matrix⁻¹ V_matrix. Both slot conventions are kept explicit. -/
def rightFormGenerator (V Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.Nondegenerate) : E →ₗ[ℝ] E :=
  leftFormGenerator V.flip Ω.flip hΩ.flip

@[simp] theorem rightFormGenerator_pairing (V Ω : LinearMap.BilinForm ℝ E)
    (hΩ : Ω.Nondegenerate) (x y : E) : Ω x (rightFormGenerator V Ω hΩ y) = V x y :=
  leftFormGenerator_pairing V.flip Ω.flip hΩ.flip y x

/-- The two actual generalized operators differ by sign for symmetric V and alternating Ω. -/
theorem leftFormGenerator_eq_neg_right (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate) :
    leftFormGenerator V Ω hΩn = -rightFormGenerator V Ω hΩn := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply hΩn.1
  intro y
  rw [map_sub,LinearMap.sub_apply]
  change Ω (leftFormGenerator V Ω hΩn x) y - Ω (-rightFormGenerator V Ω hΩn x) y = 0
  rw [map_neg,LinearMap.neg_apply,leftFormGenerator_pairing]
  have h := hΩa.neg_eq (rightFormGenerator V Ω hΩn x) y
  rw [rightFormGenerator_pairing,hV.eq y x] at h
  linarith

end GeneralizedGenerators

namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)
include d

/-- Covariance symmetry follows from the actual g-self-adjoint amplitude. -/
theorem covariance_symmetric : V.IsSymm := by
  constructor
  intro x y
  rw [d.covariance_factor,d.covariance_factor,← d.amplitude_symm,d.metric_symm.eq]

/-- Nondegeneracy of the original commutator restricted to any J-invariant subspace. -/
theorem restricted_commutator_nondegenerate (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) : (Ω.restrict U).Nondegenerate := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have h := d.complexStructure.symplectic_restrict_nondegenerate hU
  rw [d.complexStructure_symplecticForm] at h
  exact h

/-- C3-B keeps both restricted forms. K_U is exactly the g-orthogonal compression. -/
theorem restricted_covariance_identity (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    ∀ x y : U, (V.restrict U) x y = (Ω.restrict U) x
      (d.complexStructure.restrict U hU (compression d.K U y)) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  intro x y
  change V x y = Ω x (d.J (compression d.K U y))
  rw [← d.metric_eq]
  change V x y = ⟪x,compression d.K U y⟫
  rw [inner_compression]
  exact d.covariance_factor x y

/-- The independently defined right-slot generalized operator of the actual
restricted pair (V_U,Ω_U) is J_U K_U, with the manuscript's coefficient sign. -/
theorem restricted_right_generator (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    ∀ y : U,
      rightFormGenerator (V.restrict U) (Ω.restrict U) (d.restricted_commutator_nondegenerate U hU) y =
      d.complexStructure.restrict U hU (compression d.K U y) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  intro y
  apply sub_eq_zero.mp
  apply (d.restricted_commutator_nondegenerate U hU).2
  intro x
  rw [map_sub,rightFormGenerator_pairing,← d.restricted_covariance_identity U hU,sub_self]

/-- The left-slot duality convention has the opposite sign, recorded explicitly. -/
theorem restricted_left_generator (hΩa : Ω.IsAlt) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    ∀ y : U,
      leftFormGenerator (V.restrict U) (Ω.restrict U) (d.restricted_commutator_nondegenerate U hU) y =
      -d.complexStructure.restrict U hU (compression d.K U y) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  intro y
  rw [leftFormGenerator_eq_neg_right _ _ (d.covariance_symmetric.restrict U)
    (show (Ω.restrict U).IsAlt from fun x => hΩa x),LinearMap.neg_apply,
    d.restricted_right_generator U hU]

/-- Squaring the actual generalized restricted generator recovers K_U². -/
theorem restricted_right_generator_neg_square (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    let G := rightFormGenerator (V.restrict U) (Ω.restrict U)
      (d.restricted_commutator_nondegenerate U hU);
    -(G*G) = compression d.K U * compression d.K U := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  dsimp only
  apply LinearMap.ext
  intro x
  change -rightFormGenerator (V.restrict U) (Ω.restrict U)
      (d.restricted_commutator_nondegenerate U hU)
      (rightFormGenerator (V.restrict U) (Ω.restrict U)
        (d.restricted_commutator_nondegenerate U hU) x) =
    compression d.K U (compression d.K U x)
  rw [d.restricted_right_generator U hU,d.restricted_right_generator U hU,
    ← d.complexStructure.compression_commute U hU d.K d.commute,
    (d.complexStructure.restrict U hU).square_neg,neg_neg]

end BosonicAdaptationData

end Gaussian.Phase
