import Gaussian.Phase.PairedFrame

/-! Auxiliary orthogonal orbits of pure real covariance generators.
The physical subspace is arbitrary; no rank assumption is imposed on its
coupling to the auxiliary subspace. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section EqualGram
variable {D E F : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Equal Gram forms induce an isometry between the actual ranges, even when
both maps have a nontrivial kernel. -/
theorem exists_range_isometry_of_inner_eq (f : D →ₗ[ℝ] E) (g : D →ₗ[ℝ] F)
    (h : ∀ x y, ⟪f x,f y⟫ = ⟪g x,g y⟫) :
    ∃ e : LinearMap.range f ≃ₗᵢ[ℝ] LinearMap.range g,
      ∀ x, (e ⟨f x,LinearMap.mem_range_self f x⟩ : F) = g x := by
  have hk : LinearMap.ker f ≤ LinearMap.ker g.rangeRestrict := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change g x = 0
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← h x x,LinearMap.mem_ker.mp hx,inner_zero_left]
  let l : LinearMap.range f →ₗ[ℝ] LinearMap.range g :=
    ((LinearMap.ker f).liftQ g.rangeRestrict hk).comp
      f.quotKerEquivRange.symm.toLinearMap
  have hl (x : D) (hx : f x ∈ LinearMap.range f) : (l ⟨f x,hx⟩ : F) = g x := by
    simp [l]
  have hi : ∀ x y, ⟪l x,l y⟫ = ⟪x,y⟫ := by
    rintro ⟨x,⟨a,rfl⟩⟩ ⟨y,⟨b,rfl⟩⟩
    change ⟪(l _ : F),(l _ : F)⟫ = ⟪f a,f b⟫
    erw [hl a,hl b,h]
  have hs : Function.Surjective l := by
    rintro ⟨y,⟨x,rfl⟩⟩
    refine ⟨⟨f x,LinearMap.mem_range_self f x⟩,?_⟩
    apply Subtype.ext
    exact hl x _
  exact ⟨LinearIsometryEquiv.ofSurjective (l.isometryOfInner hi) hs,fun x => hl x _⟩
end EqualGram

namespace OrthogonalComplexStructure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The synthesis map for the physical space together with its J-image. -/
def hullMap (J : OrthogonalComplexStructure E) (A : Submodule ℝ E) : A × A →ₗ[ℝ] E :=
  A.subtype.coprod (J.linear.comp A.subtype)

@[simp] theorem hullMap_apply (J : OrthogonalComplexStructure E) (A : Submodule ℝ E)
    (x : A × A) : J.hullMap A x = (x.1 : E) + J x.2 := rfl

/-- The range formulation makes kernel degeneracies explicit. -/
abbrev hull (J : OrthogonalComplexStructure E) (A : Submodule ℝ E) : Submodule ℝ E :=
  LinearMap.range (J.hullMap A)

theorem mem_hull (J : OrthogonalComplexStructure E) (A : Submodule ℝ E) (x : A) :
    (x : E) ∈ J.hull A := ⟨(x,0),by simp⟩

theorem hull_invariant (J : OrthogonalComplexStructure E) (A : Submodule ℝ E) :
    J.IsInvariant (J.hull A) := by
  rintro x ⟨⟨a,b⟩,rfl⟩
  refine ⟨(-b,a),?_⟩
  simp [hullMap_apply,add_comm]

/-- Equal physical compression determines the Gram form of the entire J-hull. -/
theorem hullMap_inner_eq (J₁ J₂ : OrthogonalComplexStructure E) (A : Submodule ℝ E)
    (h : ∀ x ∈ A, ∀ y ∈ A, ⟪J₁ x,y⟫ = ⟪J₂ x,y⟫) (x y : A × A) :
    ⟪J₁.hullMap A x,J₁.hullMap A y⟫ = ⟪J₂.hullMap A x,J₂.hullMap A y⟫ := by
  simp only [hullMap_apply,inner_add_left,inner_add_right,J₁.inner_map_map,J₂.inner_map_map]
  rw [h x.2 x.2.property y.1 y.1.property]
  have hh : ⟪(x.1 : E),J₁ y.2⟫ = ⟪(x.1 : E),J₂ y.2⟫ := by
    calc
      _ = ⟪J₁ y.2,(x.1 : E)⟫ := real_inner_comm _ _
      _ = ⟪J₂ y.2,(x.1 : E)⟫ := h y.2 y.2.property x.1 x.1.property
      _ = _ := real_inner_comm _ _
  rw [hh]

/-- The forced isometry on the physical J-hull fixes physical vectors and
intertwines J. It is defined without selecting a cross-block inverse. -/
theorem exists_hull_intertwiner (J₁ J₂ : OrthogonalComplexStructure E)
    (A : Submodule ℝ E)
    (h : ∀ x ∈ A, ∀ y ∈ A, ⟪J₁ x,y⟫ = ⟪J₂ x,y⟫) :
    ∃ e : J₁.hull A ≃ₗᵢ[ℝ] J₂.hull A,
      (∀ x : A, (e ⟨x,J₁.mem_hull A x⟩ : E) = x) ∧
      (∀ x : J₁.hull A,
        (e ⟨J₁ x,J₁.hull_invariant A x x.property⟩ : E) = J₂ (e x)) := by
  obtain ⟨e,he⟩ := exists_range_isometry_of_inner_eq
    (J₁.hullMap A) (J₂.hullMap A) (J₁.hullMap_inner_eq J₂ A h)
  refine ⟨e,?_,?_⟩
  · intro x
    convert he (x,0) using 1 <;> simp
  · rintro ⟨x,⟨⟨a,b⟩,rfl⟩⟩
    have he' := he (-b,a)
    have he'' := he (a,b)
    have hs : J₁ (J₁.hullMap A (a,b)) = J₁.hullMap A (-b,a) := by simp [add_comm]
    simp only [hs]
    erw [he',he'']
    simp [add_comm]


/-- All orthogonal complex structures of the same finite real dimension are
orthogonally equivalent. The paired-frame proof includes the zero space. -/
theorem exists_intertwiner_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (J₁ : OrthogonalComplexStructure E) (J₂ : OrthogonalComplexStructure F)
    (hd : finrank ℝ E = finrank ℝ F) :
    ∃ e : E ≃ₗᵢ[ℝ] F, ∀ x, e (J₁ x) = J₂ (e x) := by
  obtain ⟨n,hn⟩ := J₁.even_finrank
  have hn₁ : finrank ℝ E = 2*n := by omega
  have hn₂ : finrank ℝ F = 2*n := by omega
  obtain ⟨b⟩ := exists_pairedEigenframe_dim n E hn₁ J₁ 0
    (by intro x y; simp) (by intro x; simp)
  obtain ⟨c⟩ := exists_pairedEigenframe_dim n F hn₂ J₂ 0
    (by intro x y; simp) (by intro x; simp)
  let e : E ≃ₗᵢ[ℝ] F :=
    Orthonormal.equiv (v := b.basis.toBasis) (v' := c.basis.toBasis)
      b.basis.orthonormal c.basis.orthonormal (Equiv.refl _)
  have he (i : Fin n × Fin 2) : e (b.basis i) = c.basis i := by
    exact Orthonormal.equiv_apply (v := b.basis.toBasis) (v' := c.basis.toBasis)
      b.basis.orthonormal c.basis.orthonormal (Equiv.refl _) i
  have hlin : e.toLinearEquiv.toLinearMap.comp J₁.linear =
      J₂.linear.comp e.toLinearEquiv.toLinearMap := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change e (J₁ (b.basis (i,k))) = J₂ (e (b.basis (i,k)))
    fin_cases k
    · change e (J₁ (b.basis (i,0))) = J₂ (e (b.basis (i,0)))
      erw [b.partner,he,he,c.partner]
    · change e (J₁ (b.basis (i,1))) = J₂ (e (b.basis (i,1)))
      erw [b.partner_second,map_neg,he,he,c.partner_second]
  exact ⟨e,fun x => LinearMap.congr_fun hlin x⟩

/-- Glue independent orthogonal maps on two orthogonal decompositions. -/
def glueOrthogonal [FiniteDimensional ℝ E] (P Q : Submodule ℝ E)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) : E ≃ₗᵢ[ℝ] E :=
  (P.orthogonalDecomposition.trans (e.withLpProdCongr 2 f)).trans
    Q.orthogonalDecomposition.symm

theorem glueOrthogonal_apply_add [FiniteDimensional ℝ E] (P Q : Submodule ℝ E)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) (x : P) (y : Pᗮ) :
    glueOrthogonal P Q e f ((x : E)+(y : E)) = (e x : E)+(f y : E) := by
  have hs : (x : E)+(y : E) = P.orthogonalDecomposition.symm (.toLp 2 (x,y)) := by
    simp
  rw [hs]
  change Q.orthogonalDecomposition.symm ((e.withLpProdCongr 2 f)
    (P.orthogonalDecomposition (P.orthogonalDecomposition.symm (.toLp 2 (x,y))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem glueOrthogonal_apply_left [FiniteDimensional ℝ E] (P Q : Submodule ℝ E)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) (x : P) :
    glueOrthogonal P Q e f x = (e x : E) := by
  simpa using glueOrthogonal_apply_add P Q e f x 0

theorem glueOrthogonal_apply_right [FiniteDimensional ℝ E] (P Q : Submodule ℝ E)
    (e : P ≃ₗᵢ[ℝ] Q) (f : Pᗮ ≃ₗᵢ[ℝ] Qᗮ) (x : Pᗮ) :
    glueOrthogonal P Q e f x = (f x : E) := by
  simpa using glueOrthogonal_apply_add P Q e f 0 x


/-- Two pure real covariance generators with equal physical compression differ
by an orthogonal map acting identically on the physical subspace. This covers
rank-deficient couplings, uncoupled pure factors, and zero dimensions. -/
theorem exists_intertwiner_fixing_subspace [FiniteDimensional ℝ E]
    (J₁ J₂ : OrthogonalComplexStructure E) (A : Submodule ℝ E)
    (h : ∀ x ∈ A, ∀ y ∈ A, ⟪J₁ x,y⟫ = ⟪J₂ x,y⟫) :
    ∃ R : E ≃ₗᵢ[ℝ] E,
      (∀ x ∈ A, R x = x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) := by
  obtain ⟨e,heA,heJ⟩ := J₁.exists_hull_intertwiner J₂ A h
  let P := J₁.hull A
  let Q := J₂.hull A
  have hP : J₁.IsInvariant P := J₁.hull_invariant A
  have hQ : J₂.IsInvariant Q := J₂.hull_invariant A
  have hP' : J₁.IsInvariant Pᗮ := J₁.orthogonal_invariant hP
  have hQ' : J₂.IsInvariant Qᗮ := J₂.orthogonal_invariant hQ
  have hd : finrank ℝ Pᗮ = finrank ℝ Qᗮ := by
    have hedim := e.toLinearEquiv.finrank_eq
    have hpd := P.finrank_add_finrank_orthogonal
    have hqd := Q.finrank_add_finrank_orthogonal
    change finrank ℝ P = finrank ℝ Q at hedim
    omega
  obtain ⟨f,hfJ⟩ := (J₁.restrict Pᗮ hP').exists_intertwiner_of_finrank_eq
    (J₂.restrict Qᗮ hQ') hd
  let R := glueOrthogonal P Q e f
  have hRl (x : P) : R x = (e x : E) := glueOrthogonal_apply_left P Q e f x
  have hRr (x : Pᗮ) : R x = (f x : E) := glueOrthogonal_apply_right P Q e f x
  refine ⟨R,?_,?_⟩
  · intro x hx
    exact (hRl ⟨x,J₁.mem_hull A ⟨x,hx⟩⟩).trans (heA ⟨x,hx⟩)
  · intro x
    have hl (p : P) : R (J₁ p) = J₂ (R p) := by
      calc
        _ = (e ⟨J₁ p,hP p p.property⟩ : E) := hRl _
        _ = J₂ (e p) := heJ p
        _ = _ := congrArg J₂ (hRl p).symm
    have hr (q : Pᗮ) : R (J₁ q) = J₂ (R q) := by
      calc
        _ = (f (J₁.restrict Pᗮ hP' q) : E) := hRr _
        _ = (J₂.restrict Qᗮ hQ' (f q) : E) := congrArg Subtype.val (hfJ q)
        _ = _ := congrArg J₂ (hRr q).symm
    let p := P.orthogonalProjectionOnto x
    let q := Pᗮ.orthogonalProjectionOnto x
    have hx : (p : E)+(q : E) = x := P.starProjection_add_starProjection_orthogonal x
    rw [← hx,J₁.apply_add,map_add,hl,hr,← J₂.apply_add,← map_add]


/-- An orthogonal map fixing the physical space restricts to a genuine
surjective orthogonal equivalence of the auxiliary complement. -/
def auxiliaryRestriction [FiniteDimensional ℝ E] (R : E ≃ₗᵢ[ℝ] E)
    (A : Submodule ℝ E) (hR : ∀ x ∈ A, R x = x) : Aᗮ ≃ₗᵢ[ℝ] Aᗮ := by
  have hm : ∀ x ∈ Aᗮ, R x ∈ Aᗮ := by
    intro x hx a ha
    calc
      ⟪a,R x⟫ = ⟪R a,R x⟫ := by rw [hR a ha]
      _ = ⟪a,x⟫ := R.inner_map_map a x
      _ = 0 := hx a ha
  let l : Aᗮ →ₗᵢ[ℝ] Aᗮ :=
    { toLinearMap := R.toLinearEquiv.toLinearMap.restrict hm
      norm_map' := fun x => R.norm_map x }
  exact LinearIsometryEquiv.ofSurjective l
    (LinearMap.surjective_of_injective l.injective)

@[simp] theorem auxiliaryRestriction_apply [FiniteDimensional ℝ E]
    (R : E ≃ₗᵢ[ℝ] E) (A : Submodule ℝ E) (hR : ∀ x ∈ A, R x = x) (x : Aᗮ) :
    (auxiliaryRestriction R A hR x : E) = R x := rfl

/-- Explicit identity-on-physical, orthogonal-on-auxiliary form of the orbit
map. The auxiliary dimension can be arbitrary, including zero. -/
theorem exists_auxiliary_orthogonal_orbit [FiniteDimensional ℝ E]
    (J₁ J₂ : OrthogonalComplexStructure E) (A : Submodule ℝ E)
    (h : ∀ x ∈ A, ∀ y ∈ A, ⟪J₁ x,y⟫ = ⟪J₂ x,y⟫) :
    ∃ (R : E ≃ₗᵢ[ℝ] E) (Q : Aᗮ ≃ₗᵢ[ℝ] Aᗮ),
      (∀ x ∈ A, R x = x) ∧ (∀ x, R (J₁ x) = J₂ (R x)) ∧
      (∀ (a : A) (c : Aᗮ), R ((a : E)+(c : E)) = (a : E)+(Q c : E)) := by
  obtain ⟨R,hR,hJ⟩ := J₁.exists_intertwiner_fixing_subspace J₂ A h
  refine ⟨R,auxiliaryRestriction R A hR,hR,hJ,?_⟩
  intro a c
  rw [map_add,hR a a.property,auxiliaryRestriction_apply]


end OrthogonalComplexStructure
end Gaussian.Phase
