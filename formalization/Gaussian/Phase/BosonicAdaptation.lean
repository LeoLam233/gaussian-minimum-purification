import Gaussian.Phase.SkewAdaptation

/-! Adaptation of a nondegenerate alternating form relative to a positive
covariance metric.  All conclusions are derived from raw forms. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section AlgebraicData
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Algebraic output of the bosonic adaptation construction. The metric is
identified with the original Ω and J; the covariance is identified with gK.
The existence theorem below constructs all fields from raw forms. -/
structure BosonicAdaptationData (V Ω : LinearMap.BilinForm ℝ E) where
  J : E →ₗ[ℝ] E
  K : E →ₗ[ℝ] E
  g : LinearMap.BilinForm ℝ E
  square_neg : ∀ x, J (J x) = -x
  metric_eq : ∀ x y, g x y = Ω x (J y)
  metric_symm : g.IsSymm
  metric_pos : ∀ x, x ≠ 0 → 0 < g x x
  covariance_factor : ∀ x y, V x y = g x (K y)
  covariance_isometry : ∀ x y, V (J x) (J y) = V x y
  symplectic_isometry : ∀ x y, Ω (J x) (J y) = Ω x y
  commute : ∀ x, J (K x) = K (J x)
  amplitude_symm : ∀ x y, g (K x) y = g x (K y)

end AlgebraicData

section InnerMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem innerForm_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)

/-- The unique generator T satisfying Ω(x,y)=V(x,Ty), where V is the
present inner product. This is the coordinate-free form of V⁻¹Ω. -/
def formGenerator (Ω : LinearMap.BilinForm ℝ E) : E →ₗ[ℝ] E :=
  (LinearMap.BilinForm.toDual (innerₗ E) innerForm_nondegenerate).symm.toLinearMap ∘ₗ Ω.flip

@[simp] theorem inner_formGenerator (Ω : LinearMap.BilinForm ℝ E) (x y : E) :
    ⟪x,formGenerator Ω y⟫ = Ω x y := by
  have h := congrArg (fun f : Module.Dual ℝ E => f x)
    ((LinearMap.BilinForm.toDual (innerₗ E) innerForm_nondegenerate).apply_symm_apply (Ω.flip y))
  change ⟪formGenerator Ω y,x⟫ = Ω x y at h
  rwa [real_inner_comm] at h

theorem formGenerator_skew (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) :
    IsSkew (formGenerator Ω) := by
  intro x y
  rw [real_inner_comm,inner_formGenerator,inner_formGenerator]
  exact (hΩ.neg_eq x y).symm

theorem formGenerator_injective (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.Nondegenerate) :
    Function.Injective (formGenerator Ω) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hΩ.2
  intro z
  rw [map_sub]
  rw [← inner_formGenerator Ω z x,← inner_formGenerator Ω z y,hxy,sub_self]

/-- The real quadratic uncertainty inequality makes V⁻¹Ω a contraction in V. -/
theorem formGenerator_contracts (Ω : LinearMap.BilinForm ℝ E)
    (hUnc : ∀ x y, (Ω x y)^2 ≤ ⟪x,x⟫ * ⟪y,y⟫) :
    ∀ x, ‖formGenerator Ω x‖ ≤ ‖x‖ := by
  intro x
  let y := formGenerator Ω x
  by_cases hy : y = 0
  · simpa [y,hy] using norm_nonneg x
  have h := hUnc y x
  rw [← inner_formGenerator Ω y x] at h
  change ⟪y,y⟫^2 ≤ ⟪y,y⟫*⟪x,x⟫ at h
  have hyy : 0 < ⟪y,y⟫ := real_inner_self_pos.mpr hy
  have hle : ⟪y,y⟫ ≤ ⟪x,x⟫ := by nlinarith
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hle
  exact (sq_le_sq₀ (norm_nonneg y) (norm_nonneg x)).mp hle

/-- Build a bosonic compatible metric and inverse amplitude from a raw
nondegenerate alternating form and an arbitrary even-dimensional positive
inner product. The sign J=-J_T is forced by Ω(x,Jx)>0. -/
def bosonicAdaptationOfInner (Ω : LinearMap.BilinForm ℝ E) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hEven : Even (finrank ℝ E)) :
    BosonicAdaptationData (innerₗ E) Ω := by
  let T := formGenerator Ω
  let d := Classical.choice (exists_skewAdaptation T (formGenerator_skew Ω hΩa) hEven)
  have hTi : Function.Injective T := formGenerator_injective Ω hΩn
  let k := LinearEquiv.ofInjectiveEndo d.K (d.K_injective hTi)
  have hk : ∀ x, d.K (k.symm x) = x := k.apply_symm_apply
  have hki : ∀ x, k.symm (d.K x) = x := k.symm_apply_apply
  have hTJ : ∀ x, T (-d.J x) = d.K x := by
    intro x
    rw [map_neg, d.factor, ← d.commute, d.square_neg, neg_neg]
  let g : LinearMap.BilinForm ℝ E := (innerₗ E).compl₂ d.K
  have hg : ∀ x y, g x y = Ω x (-d.J y) := by
    intro x y
    rw [← inner_formGenerator Ω x (-d.J y)]
    change ⟪x,d.K y⟫ = ⟪x,T (-d.J y)⟫
    rw [hTJ]
  refine {
    J := -d.J
    K := k.symm.toLinearMap
    g := g
    square_neg := ?_
    metric_eq := hg
    metric_symm := ?_
    metric_pos := ?_
    covariance_factor := ?_
    covariance_isometry := ?_
    symplectic_isometry := ?_
    commute := ?_
    amplitude_symm := ?_ }
  · intro x
    simp only [LinearMap.neg_apply, map_neg, d.square_neg, neg_neg]
  · constructor
    intro x y
    change ⟪x,d.K y⟫ = ⟪y,d.K x⟫
    rw [← d.positive.isSymmetric,real_inner_comm]
  · intro x hx
    change 0 < ⟪x,d.K x⟫
    rw [real_inner_comm]
    exact d.K_inner_pos hTi hx
  · intro x y
    change ⟪x,y⟫ = ⟪x,d.K (k.symm y)⟫
    rw [hk]
  · intro x y
    change ⟪-d.J x,-d.J y⟫ = ⟪x,y⟫
    rw [inner_neg_left,inner_neg_right,neg_neg,d.inner_map_map]
  · intro x y
    change Ω (-d.J x) (-d.J y) = Ω x y
    rw [← inner_formGenerator Ω (-d.J x) (-d.J y), ← inner_formGenerator Ω x y]
    change ⟪-d.J x,T (-d.J y)⟫ = ⟪x,T y⟫
    rw [hTJ,inner_neg_left,d.skew,neg_neg,← d.factor]
  · intro x
    change -d.J (k.symm x) = k.symm (-d.J x)
    apply d.K_injective hTi
    rw [map_neg, ← d.commute,hk,hk]
  · intro x y
    change ⟪k.symm x,d.K y⟫ = ⟪x,d.K (k.symm y)⟫
    rw [← d.positive.isSymmetric,hk,hk]

/-- Uncertainty yields the bosonic lower endpoint g≤V, equivalently K≥I in g. -/
theorem bosonicAdaptationOfInner_lower (Ω : LinearMap.BilinForm ℝ E)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate) (hEven : Even (finrank ℝ E))
    (hUnc : ∀ x y, (Ω x y)^2 ≤ ⟪x,x⟫ * ⟪y,y⟫) (x : E) :
    (bosonicAdaptationOfInner Ω hΩa hΩn hEven).g x x ≤ ⟪x,x⟫ := by
  let d := Classical.choice (exists_skewAdaptation (formGenerator Ω)
    (formGenerator_skew Ω hΩa) hEven)
  have h := (d.one_sub_positive (formGenerator_contracts Ω hUnc)).inner_nonneg_left x
  change 0 ≤ ⟪x-d.K x,x⟫ at h
  rw [inner_sub_left] at h
  change ⟪x,d.K x⟫ ≤ ⟪x,x⟫
  have hc := real_inner_comm x (d.K x)
  linarith

end InnerMetric
section RawForms
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A raw strictly positive symmetric covariance form induces a genuine real
inner-product space, without imposing a global covariance or squeezing bound. -/
def covarianceInnerCore (V : LinearMap.BilinForm ℝ E) (hVs : V.IsSymm)
    (hVp : ∀ x, x ≠ 0 → 0 < V x x) : InnerProductSpace.Core ℝ E where
  inner x y := V x y
  conj_inner_symm x y := by simpa using hVs.eq y x
  re_inner_nonneg x := by
    change 0 ≤ V x x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hVp x hx).le
  add_left x y z := by simp only [map_add,LinearMap.add_apply]
  smul_left x y r := by simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,RCLike.conj_to_real]
  definite x hx := by
    by_contra h
    exact (ne_of_gt (hVp x h)) hx

/-- Raw bosonic coefficient-space adaptation. Inputs are only a strictly positive
covariance form V, a nondegenerate alternating commutator Ω, even finite real
dimension, and the quadratic uncertainty inequality. The constructed metric is
ΩJ, and the constructed amplitude satisfies V=gK and K≥I in g. -/
theorem exists_bosonicAdaptation (V Ω : LinearMap.BilinForm ℝ E)
    (hVs : V.IsSymm) (hVp : ∀ x, x ≠ 0 → 0 < V x x)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate) (hEven : Even (finrank ℝ E))
    (hUnc : ∀ x y, (Ω x y)^2 ≤ V x x * V y y) :
    ∃ d : BosonicAdaptationData V Ω, ∀ x, d.g x x ≤ V x x := by
  let core := covarianceInnerCore V hVs hVp
  letI : NormedAddCommGroup E := core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  have hV : (innerₗ E : LinearMap.BilinForm ℝ E) = V := by ext x y; rfl
  let d := bosonicAdaptationOfInner Ω hΩa hΩn hEven
  have h : ∃ d : BosonicAdaptationData (innerₗ E) Ω, ∀ x, d.g x x ≤ V x x := by
    refine ⟨d,fun x => ?_⟩
    exact bosonicAdaptationOfInner_lower Ω hΩa hΩn hEven hUnc x
  change ∃ d : BosonicAdaptationData V Ω, ∀ x, d.g x x ≤ V x x at h
  exact h

end RawForms

namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

theorem metric_isometry (x y : E) : d.g (d.J x) (d.J y) = d.g x y := by
  rw [d.metric_eq,d.metric_eq]
  exact d.symplectic_isometry x (d.J y)

/-- The constructed compatible metric as an actual inner-product-space core. -/
@[instance_reducible] def metricCore : InnerProductSpace.Core ℝ E :=
  covarianceInnerCore d.g d.metric_symm d.metric_pos

/-- J packaged as an isometry for the actual compatible metric g=ΩJ. -/
def complexStructure :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    OrthogonalComplexStructure E := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  exact {
    equiv := LinearIsometryEquiv.ofSurjective
      { toLinearMap := d.J
        norm_map' := fun x => by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
            ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
          exact d.metric_isometry x x }
      (fun x => ⟨-d.J x, by simp [d.square_neg]⟩)
    square_neg := d.square_neg }

/-- The induced form from the compatible geometry is the original Ω, not an
unrelated auxiliary symplectic form. -/
theorem complexStructure_symplecticForm :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    d.complexStructure.symplecticForm = Ω := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  ext x y
  change -d.g x (d.J y) = Ω x y
  rw [d.metric_eq,d.square_neg,map_neg,neg_neg]

/-- Positive self-adjointness of the actual bosonic amplitude in g. -/
theorem amplitude_positive (hVp : ∀ x, x ≠ 0 → 0 < V x x) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    d.K.IsPositive := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  refine ⟨d.amplitude_symm,?_⟩
  intro x
  change 0 ≤ d.g (d.K x) x
  rw [d.amplitude_symm,← d.covariance_factor]
  by_cases hx : x = 0
  · simp [hx]
  · exact (hVp x hx).le

/-- The lower endpoint is an actual positive operator inequality in g. -/
theorem amplitude_sub_one_positive (hLower : ∀ x, d.g x x ≤ V x x) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    (d.K-LinearMap.id).IsPositive := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  refine ⟨(show d.K.IsSymmetric from d.amplitude_symm).sub LinearMap.IsSymmetric.id,?_⟩
  intro x
  change 0 ≤ d.g (d.K x-x) x
  rw [map_sub,LinearMap.sub_apply,d.amplitude_symm,← d.covariance_factor]
  exact sub_nonneg.mpr (hLower x)

/-- Sector-correct C2 crosswalk for the original Ω and the constructed J. -/
theorem hull_symplectic_orthogonal (A : Submodule ℝ E) :
    Ω.orthogonal (A ⊔ A.map d.J) = Ω.orthogonal A ⊓ (Ω.orthogonal A).map d.J := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have h := d.complexStructure.symplectic_hull_orthogonal A
  rw [d.complexStructure_symplecticForm] at h
  exact h

/-- The compatible-metric complement agrees with the actual symplectic
complement on every invariant subspace. -/
theorem metric_orthogonal_eq {A : Submodule ℝ E} (hA : ∀ x ∈ A, d.J x ∈ A) :
    d.g.orthogonal A = Ω.orthogonal A := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have h := d.complexStructure.symplectic_orthogonal_eq hA
  rw [d.complexStructure_symplecticForm] at h
  exact h.symm

/-- The selected real coefficient plane, defined without a norm instance. -/
def selectedPlane (v : E) : Submodule ℝ E := Submodule.span ℝ ({v,d.J v} : Set E)

/-- A genuine excess-mode plane for the original bosonic forms, together with
its nondegenerate retained complement and the precise compatible metric. -/
theorem exists_selected_plane (C : Submodule ℝ E) (hC : finrank ℝ E < 2*finrank ℝ C) :
    ∃ v : E, v ≠ 0 ∧ d.selectedPlane v ≤ C ∧
      finrank ℝ (d.selectedPlane v) = 2 ∧
      (∀ x ∈ d.selectedPlane v, d.J x ∈ d.selectedPlane v) ∧
      (∀ x ∈ Ω.orthogonal (d.selectedPlane v), d.J x ∈ Ω.orthogonal (d.selectedPlane v)) ∧
      (Ω.restrict (d.selectedPlane v)).Nondegenerate ∧
      (Ω.restrict (Ω.orthogonal (d.selectedPlane v))).Nondegenerate ∧
      IsCompl (d.selectedPlane v) (Ω.orthogonal (d.selectedPlane v)) ∧
      d.g.orthogonal (d.selectedPlane v) = Ω.orthogonal (d.selectedPlane v) := by
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  obtain ⟨v,hv,hPC,hd,hP,hU⟩ := d.complexStructure.exists_plane_of_excess C hC
  have hs := d.complexStructure.plane_symplectic_split v
  rw [d.complexStructure_symplecticForm] at hs
  have ho := d.complexStructure.symplectic_orthogonal_eq hP
  rw [d.complexStructure_symplecticForm] at ho
  refine ⟨v,hv,hPC,hd,hP,?_,hs.1,hs.2.1,hs.2.2,?_⟩
  · change d.complexStructure.IsInvariant (Ω.orthogonal (d.complexStructure.plane v))
    rw [ho]
    exact hU
  · exact d.metric_orthogonal_eq hP

end BosonicAdaptationData

end Gaussian.Phase
