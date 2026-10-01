import Gaussian.Phase.BosonicPurificationProduct
import Gaussian.Phase.BosonicPurificationSymplectic

/-! Exact product-subspace geometry for protected cuts and pure-mode deletion.
These lemmas identify the real retained subspaces rather than assuming a
coordinate factorization or a nondegenerate compression. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Nondegeneracy of a product implies nondegeneracy on its literal first factor. -/
theorem productForm_nondegenerate_left (Ω : LinearMap.BilinForm ℝ E)
    (σ : LinearMap.BilinForm ℝ F) (h : (productForm Ω σ).Nondegenerate) : Ω.Nondegenerate := by
  constructor
  · intro x hx
    have he : ((x,0) : E × F)=0 := h.1 (x,0) (fun y => by simp [hx y.1])
    exact congrArg Prod.fst he
  · intro x hx
    have he : ((x,0) : E × F)=0 := h.2 (x,0) (fun y => by simp [hx y.1])
    exact congrArg Prod.fst he

/-- Nondegeneracy of a product implies nondegeneracy on its literal second factor. -/
theorem productForm_nondegenerate_right (Ω : LinearMap.BilinForm ℝ E)
    (σ : LinearMap.BilinForm ℝ F) (h : (productForm Ω σ).Nondegenerate) : σ.Nondegenerate := by
  constructor
  · intro x hx
    have he : ((0,x) : E × F)=0 := h.1 (0,x) (fun y => by simp [hx y.2])
    exact congrArg Prod.snd he
  · intro x hx
    have he : ((0,x) : E × F)=0 := h.2 (0,x) (fun y => by simp [hx y.2])
    exact congrArg Prod.snd he

/-- An exact product decomposition has a nondegenerate form precisely when both factors do. -/
theorem productForm_nondegenerate_iff (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F) :
    (productForm Ω σ).Nondegenerate ↔ Ω.Nondegenerate ∧ σ.Nondegenerate :=
  ⟨fun h => ⟨productForm_nondegenerate_left Ω σ h,productForm_nondegenerate_right Ω σ h⟩,
    fun h => productForm_nondegenerate h.1 h.2⟩

/-- Pullback through an actual linear equivalence preserves nondegeneracy. -/
theorem form_nondegenerate_pullback_iff (Ω : LinearMap.BilinForm ℝ E) (L : F ≃ₗ[ℝ] E) :
    (Ω.compl₁₂ L.toLinearMap L.toLinearMap).Nondegenerate ↔ Ω.Nondegenerate := by
  constructor
  · intro h
    exact nondegenerate_of_form_equiv _ Ω h L (fun x y => rfl)
  · intro h
    apply nondegenerate_of_form_equiv Ω _ h L.symm
    intro x y
    change Ω (L (L.symm x)) (L (L.symm y)) = Ω x y
    rw [L.apply_symm_apply,L.apply_symm_apply]

/-- Every subspace containing the entire first factor splits literally as that
factor times its actual zero-first-coordinate slice. -/
def protectedProductEquiv (U : Submodule ℝ (E × F))
    (hU : (LinearMap.inl ℝ E F).range ≤ U) :
    (E × U.comap (LinearMap.inr ℝ E F)) ≃ₗ[ℝ] U := by
  let S := U.comap (LinearMap.inr ℝ E F)
  have hs : ∀ u : U, u.val.2 ∈ S := by
    intro u
    have h := U.sub_mem u.property (hU ⟨u.val.1,rfl⟩)
    change (u.val.1-u.val.1,u.val.2-0) ∈ U at h
    change (0,u.val.2) ∈ U
    simpa using h
  let f : (E × S) →ₗ[ℝ] (E × F) := (LinearMap.id : E →ₗ[ℝ] E).prodMap S.subtype
  have hf : ∀ x, f x ∈ U := by
    intro x
    have h := U.add_mem (hU ⟨x.1,rfl⟩) x.2.property
    change (x.1+0,0+(x.2 : F)) ∈ U at h
    change (x.1,(x.2 : F)) ∈ U
    simpa using h
  exact {
    toLinearMap := f.codRestrict U hf
    invFun := fun u => (u.val.1,⟨u.val.2,hs u⟩)
    left_inv := fun x => by apply Prod.ext <;> rfl
    right_inv := fun x => by apply Subtype.ext; rfl }

@[simp] theorem protectedProductEquiv_apply (U : Submodule ℝ (E × F))
    (hU : (LinearMap.inl ℝ E F).range ≤ U) (x : E × U.comap (LinearMap.inr ℝ E F)) :
    (protectedProductEquiv U hU x : E × F) = (x.1,(x.2 : F)) := rfl

theorem protectedProductEquiv_finrank [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (U : Submodule ℝ (E × F)) (hU : (LinearMap.inl ℝ E F).range ≤ U) :
    finrank ℝ U = finrank ℝ E + finrank ℝ (U.comap (LinearMap.inr ℝ E F)) := by
  rw [← (protectedProductEquiv U hU).finrank_eq,Module.finrank_prod]

/-- The retained zero-first slice is genuinely nondegenerate when the actual
retained product subspace is nondegenerate. -/
theorem protectedProduct_nondegenerate_slice (Ω : LinearMap.BilinForm ℝ E)
    (σ : LinearMap.BilinForm ℝ F) (U : Submodule ℝ (E × F))
    (hU : (LinearMap.inl ℝ E F).range ≤ U) (hnd : ((productForm Ω σ).restrict U).Nondegenerate) :
    (σ.restrict (U.comap (LinearMap.inr ℝ E F))).Nondegenerate := by
  apply productForm_nondegenerate_right Ω
  apply nondegenerate_of_form_equiv ((productForm Ω σ).restrict U)
    (productForm Ω (σ.restrict (U.comap (LinearMap.inr ℝ E F)))) hnd
    (protectedProductEquiv U hU).symm
  intro x y
  rfl

/-- The true symplectic complement of an auxiliary-only subspace retains the
entire physical factor and exactly the true auxiliary symplectic complement. -/
theorem productForm_orthogonal_auxiliary (Ω : LinearMap.BilinForm ℝ E)
    (σ : LinearMap.BilinForm ℝ F) (P : Submodule ℝ F) :
    (productForm Ω σ).orthogonal (P.map (LinearMap.inr ℝ E F)) = (⊤ : Submodule ℝ E).prod (σ.orthogonal P) := by
  ext x
  constructor
  · intro hx
    refine ⟨Submodule.mem_top,?_⟩
    intro y hy
    have h := hx (0,y) ⟨y,hy,rfl⟩
    simpa using h
  · rintro ⟨_,hx⟩ y hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa using hx z hz

/-- Nondegeneracy on the physical factor identifies its true symplectic
complement with the literal auxiliary coordinate range. -/
theorem productForm_orthogonal_physical (Ω : LinearMap.BilinForm ℝ E)
    (σ : LinearMap.BilinForm ℝ F) (hΩ : Ω.Nondegenerate) :
    (productForm Ω σ).orthogonal (LinearMap.inl ℝ E F).range =
      (LinearMap.inr ℝ E F).range := by
  ext x
  constructor
  · intro hx
    have hfst : x.1=0 := hΩ.2 x.1 (fun a => by
      have h := hx (a,0) ⟨a,rfl⟩
      simpa using h)
    refine ⟨x.2,?_⟩
    apply Prod.ext
    · exact hfst.symm
    · rfl
  · rintro ⟨y,rfl⟩ z ⟨a,rfl⟩
    simp

/-- A genuinely auxiliary-only subspace is linearly equivalent to its literal
zero-first-coordinate slice, without choosing any basis. -/
def auxiliaryOnlyEquiv (P : Submodule ℝ (E × F))
    (hP : P ≤ (LinearMap.inr ℝ E F).range) :
    P.comap (LinearMap.inr ℝ E F) ≃ₗ[ℝ] P where
  toLinearMap := ((LinearMap.inr ℝ E F).comp (P.comap (LinearMap.inr ℝ E F)).subtype).codRestrict P
    (fun x => x.property)
  invFun x := ⟨x.val.2,by
    obtain ⟨y,hy⟩ := hP x.property
    have he : (0,x.val.2)=x.val := by
      apply Prod.ext
      · simpa only [LinearMap.inr_apply] using congrArg (fun z : E × F => z.1) hy
      · rfl
    change (0,x.val.2) ∈ P
    rw [he]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    apply Subtype.ext
    obtain ⟨y,hy⟩ := hP x.property
    apply Prod.ext
    · change (0 : E) = x.val.1
      simpa only [LinearMap.inr_apply] using congrArg (fun z : E × F => z.1) hy
    · rfl

@[simp] theorem auxiliaryOnlyEquiv_apply (P : Submodule ℝ (E × F))
    (hP : P ≤ (LinearMap.inr ℝ E F).range) (x : P.comap (LinearMap.inr ℝ E F)) :
    (auxiliaryOnlyEquiv P hP x : E × F) = (0,(x : F)) := rfl

theorem auxiliaryOnly_map_eq (P : Submodule ℝ (E × F))
    (hP : P ≤ (LinearMap.inr ℝ E F).range) :
    (P.comap (LinearMap.inr ℝ E F)).map (LinearMap.inr ℝ E F) = P := by
  exact Submodule.map_comap_eq_self hP

/-- Literal product coordinates on a subspace with unrestricted first factor. -/
def fullProductSubspaceEquiv (S : Submodule ℝ F) :
    (E × S) ≃ₗ[ℝ] (⊤ : Submodule ℝ E).prod S where
  toLinearMap := ((LinearMap.id : E →ₗ[ℝ] E).prodMap S.subtype).codRestrict _
    (fun x => ⟨Submodule.mem_top,x.2.property⟩)
  invFun x := (x.val.1,⟨x.val.2,x.property.2⟩)
  left_inv x := by apply Prod.ext <;> rfl
  right_inv x := by apply Subtype.ext; rfl

@[simp] theorem fullProductSubspaceEquiv_apply (S : Submodule ℝ F) (x : E × S) :
    (fullProductSubspaceEquiv (E := E) S x : E × F) = (x.1,(x.2 : F)) := rfl

end Gaussian.Phase
