import Gaussian.Phase.FrameExtension

/-! Orthogonal frame selection while fixing a protected coefficient subspace.
Only explicit orthogonality and finite-dimensional data are used. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Extend a frame change inside the protected orthogonal complement while
acting as the identity on the protected subspace. -/
theorem exists_protected_orthogonal_extension (A : Submodule ℝ E)
    (f g : F →ₗᵢ[ℝ] Aᗮ) :
    ∃ R : E ≃ₗᵢ[ℝ] E,
      (∀ a ∈ A, R a = a) ∧ (∀ x, R (g x : E) = (f x : E)) := by
  obtain ⟨Q,hQ⟩ := exists_orthogonal_extension f g
  let R := OrthogonalComplexStructure.glueOrthogonal A A (LinearIsometryEquiv.refl ℝ A) Q
  refine ⟨R,?_,?_⟩
  · intro a ha
    exact OrthogonalComplexStructure.glueOrthogonal_apply_left A A
      (LinearIsometryEquiv.refl ℝ A) Q ⟨a,ha⟩
  · intro x
    calc
      R (g x : E) = (Q (g x) : E) :=
        OrthogonalComplexStructure.glueOrthogonal_apply_right A A
          (LinearIsometryEquiv.refl ℝ A) Q (g x)
      _ = (f x : E) := congrArg Subtype.val (hQ x)

/-- The coordinate isometry supplied by a finite orthonormal family. -/
def orthonormalFrameIsometry {ι : Type*} [Fintype ι]
    (t : ι → E) (ht : Orthonormal ℝ t) : EuclideanSpace ℝ ι →ₗᵢ[ℝ] E :=
  ((EuclideanSpace.basisFun ι ℝ).toBasis.constr ℝ t).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun ι ℝ).toBasis) (EuclideanSpace.basisFun ι ℝ).orthonormal
    (by simpa only [Function.comp_def, Basis.constr_basis] using ht)

@[simp] theorem orthonormalFrameIsometry_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → E) (ht : Orthonormal ℝ t) (i : ι) :
    orthonormalFrameIsometry t ht (EuclideanSpace.single i 1) = t i := by
  rw [← EuclideanSpace.basisFun_apply]
  change (EuclideanSpace.basisFun ι ℝ).toBasis.constr ℝ t
    ((EuclideanSpace.basisFun ι ℝ) i) = t i
  exact Basis.constr_basis _ _ _ _

/-- Any two prescribed orthonormal families in the protected complement can
be matched by a global orthogonal map fixing every protected vector. -/
theorem exists_protected_frame_change {ι : Type*} [Fintype ι]
    (A : Submodule ℝ E) (s t : ι → E) (hs : Orthonormal ℝ s) (ht : Orthonormal ℝ t)
    (hsA : ∀ i, s i ∈ Aᗮ) (htA : ∀ i, t i ∈ Aᗮ) :
    ∃ R : E ≃ₗᵢ[ℝ] E, (∀ a ∈ A, R a = a) ∧ (∀ i, R (s i) = t i) := by
  classical
  let sA : ι → Aᗮ := fun i => ⟨s i,hsA i⟩
  let tA : ι → Aᗮ := fun i => ⟨t i,htA i⟩
  have hs' : Orthonormal ℝ sA := by
    rw [orthonormal_iff_ite] at hs ⊢
    exact hs
  have ht' : Orthonormal ℝ tA := by
    rw [orthonormal_iff_ite] at ht ⊢
    exact ht
  obtain ⟨R,hRA,hR⟩ := exists_protected_orthogonal_extension A
    (orthonormalFrameIsometry tA ht') (orthonormalFrameIsometry sA hs')
  refine ⟨R,hRA,?_⟩
  intro i
  simpa only [orthonormalFrameIsometry_single] using hR (EuclideanSpace.single i (1 : ℝ))


/-- A real invariant two-plane has a full orthonormal J-paired basis, derived
from its dimension rather than assumed as additional frame data. -/
theorem exists_paired_plane_basis (J : OrthogonalComplexStructure E)
    (P : Submodule ℝ E) (hP : J.IsInvariant P) (hd : finrank ℝ P = 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ P, J (b 0 : E) = (b 1 : E) := by
  obtain ⟨c⟩ := exists_pairedEigenframe_dim 1 P (by omega) (J.restrict P hP) 0
    (by intro x y; simp) (by intro x; simp)
  let b := c.basis.reindex (Equiv.uniqueProd (Fin 2) (Fin 1))
  have hb (i : Fin 2) : b i = c.basis (0,i) := by
    simp [b,OrthonormalBasis.reindex_apply]
  refine ⟨b,?_⟩
  rw [hb,hb]
  exact congrArg Subtype.val (c.partner 0)

/-- Place an invariant two-plane into a designated orthonormal terminal pair,
fixing the protected subspace pointwise. The conjugated complex structure acts
on that pair by the canonical rotation, so the placement retains purity. -/
theorem exists_protected_paired_plane_selection (J : OrthogonalComplexStructure E)
    (A P : Submodule ℝ E) (hP : J.IsInvariant P) (hd : finrank ℝ P = 2)
    (hPA : P ≤ Aᗮ) (t : Fin 2 → E) (ht : Orthonormal ℝ t)
    (htA : ∀ i, t i ∈ Aᗮ) :
    ∃ R : E ≃ₗᵢ[ℝ] E,
      (∀ a ∈ A, R a = a) ∧
      P.map R.toLinearEquiv.toLinearMap = Submodule.span ℝ (Set.range t) ∧
      R (J (R.symm (t 0))) = t 1 ∧
      R (J (R.symm (t 1))) = -t 0 := by
  obtain ⟨b,hb⟩ := exists_paired_plane_basis J P hP hd
  let s : Fin 2 → E := fun i => b i
  have hs : Orthonormal ℝ s := b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  have hsA (i : Fin 2) : s i ∈ Aᗮ := hPA (b i).property
  obtain ⟨R,hRA,hR⟩ := exists_protected_frame_change A s t hs ht hsA htA
  have hspan : Submodule.span ℝ (Set.range s) = P := by
    have h := congrArg (fun U : Submodule ℝ P => U.map P.subtype) b.toBasis.span_eq
    simpa only [Submodule.map_span,← Set.range_comp,Submodule.map_top,Submodule.range_subtype,
      OrthonormalBasis.coe_toBasis,Function.comp_def,Submodule.subtype_apply,s]
      using h
  have hmap : P.map R.toLinearEquiv.toLinearMap = Submodule.span ℝ (Set.range t) := by
    rw [← hspan,Submodule.map_span,← Set.range_comp]
    exact congrArg (fun v : Fin 2 → E => Submodule.span ℝ (Set.range v)) (funext hR)
  have hJs : J (s 0) = s 1 := hb
  have hJs' : J (s 1) = -s 0 := by rw [← hJs,J.apply_apply]
  refine ⟨R,hRA,hmap,?_,?_⟩
  · rw [← hR 0, R.symm_apply_apply,hJs,hR 1]
  · rw [← hR 1, R.symm_apply_apply,hJs',map_neg,hR 0]

/-- The requested auxiliary selection hypothesis P ≤ (A + JA)ᗮ implies the
orthogonality needed for the protected frame change. No restriction is imposed
on the dimension of A, and the terminal plane need not be invariant before
conjugating the global covariance generator. -/
theorem exists_protected_hull_plane_selection (J : OrthogonalComplexStructure E)
    (A P : Submodule ℝ E) (hP : J.IsInvariant P) (hd : finrank ℝ P = 2)
    (hPA : P ≤ (A ⊔ J.image A)ᗮ) (t : Fin 2 → E) (ht : Orthonormal ℝ t)
    (htA : ∀ i, t i ∈ Aᗮ) :
    ∃ R : E ≃ₗᵢ[ℝ] E,
      (∀ a ∈ A, R a = a) ∧
      P.map R.toLinearEquiv.toLinearMap = Submodule.span ℝ (Set.range t) ∧
      R (J (R.symm (t 0))) = t 1 ∧
      R (J (R.symm (t 1))) = -t 0 := by
  apply exists_protected_paired_plane_selection J A P hP hd ?_ t ht htA
  intro x hx a ha
  exact hPA hx a ((show A ≤ A ⊔ J.image A from le_sup_left) ha)



/-- Direct inverse-image identity for retained orthogonal complements. -/
theorem inverse_orthogonal_image (R : E ≃ₗᵢ[ℝ] E) (P Q : Submodule ℝ E)
    (hPQ : P.map R.toLinearEquiv.toLinearMap = Q) :
    Qᗮ.map R.symm.toLinearEquiv.toLinearMap = Pᗮ := by
  apply (Submodule.map_symm_eq_iff R.toLinearEquiv).mpr
  rw [P.map_orthogonal_equiv R,hPQ]

/-- If a coordinate embedding has range Qᗮ, pulling it back through the
orthogonal placement gives exactly the original retained subspace Pᗮ. -/
theorem range_inverse_comp_eq_orthogonal (R : E ≃ₗᵢ[ℝ] E) (P Q : Submodule ℝ E)
    (hPQ : P.map R.toLinearEquiv.toLinearMap = Q) (f : F →ₗ[ℝ] E)
    (hf : LinearMap.range f = Qᗮ) :
    LinearMap.range (R.symm.toLinearEquiv.toLinearMap.comp f) = Pᗮ := by
  rw [LinearMap.range_comp,hf]
  exact inverse_orthogonal_image R P Q hPQ

namespace OrthogonalComplexStructure
/-- The global complex structure after an orthogonal coordinate change. -/
def conjugate (J : OrthogonalComplexStructure E) (R : E ≃ₗᵢ[ℝ] E) :
    OrthogonalComplexStructure E where
  equiv := (R.symm.trans J.equiv).trans R
  square_neg x := by
    change R (J (R.symm (R (J (R.symm x))))) = -x
    rw [R.symm_apply_apply,J.apply_apply,map_neg,R.apply_symm_apply]

@[simp] theorem conjugate_apply (J : OrthogonalComplexStructure E)
    (R : E ≃ₗᵢ[ℝ] E) (x : E) : J.conjugate R x = R (J (R.symm x)) := rfl

/-- Global invariance is transported to the actual image subspace. -/
theorem conjugate_image_invariant (J : OrthogonalComplexStructure E)
    (R : E ≃ₗᵢ[ℝ] E) (P : Submodule ℝ E) (hP : J.IsInvariant P) :
    (J.conjugate R).IsInvariant (P.map R.toLinearEquiv.toLinearMap) := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨J y,hP y hy,?_⟩
  change R (J y) = R (J (R.symm (R y)))
  rw [R.symm_apply_apply]

/-- A placed invariant plane and its retained complement are both invariant
under the conjugated global generator. The retained complement is exactly the
image of the original complement; its inverse image is exactly Pᗮ. -/
theorem transport_invariant_split (J : OrthogonalComplexStructure E)
    (R : E ≃ₗᵢ[ℝ] E) (P Q : Submodule ℝ E) (hP : J.IsInvariant P)
    (hPQ : P.map R.toLinearEquiv.toLinearMap = Q) :
    (J.conjugate R).IsInvariant Q ∧ (J.conjugate R).IsInvariant Qᗮ ∧
      Pᗮ.map R.toLinearEquiv.toLinearMap = Qᗮ ∧
      Qᗮ.comap R.toLinearEquiv.toLinearMap = Pᗮ := by
  have hQ : (J.conjugate R).IsInvariant Q := by
    rw [← hPQ]
    exact J.conjugate_image_invariant R P hP
  have hc : Pᗮ.map R.toLinearEquiv.toLinearMap = Qᗮ := by
    rw [P.map_orthogonal_equiv R,hPQ]
  refine ⟨hQ,(J.conjugate R).orthogonal_invariant hQ,hc,?_⟩
  rw [← hc]
  exact Submodule.comap_map_eq_of_injective R.injective Pᗮ

/-- The pulled-back retained coordinate range is invariant under the original
complex structure, matching an actual prefix/suffix restriction interface. -/
theorem inverse_comp_range_invariant (J : OrthogonalComplexStructure E)
    (R : E ≃ₗᵢ[ℝ] E) (P Q : Submodule ℝ E) (hP : J.IsInvariant P)
    (hPQ : P.map R.toLinearEquiv.toLinearMap = Q) (f : F →ₗ[ℝ] E)
    (hf : LinearMap.range f = Qᗮ) :
    J.IsInvariant (LinearMap.range (R.symm.toLinearEquiv.toLinearMap.comp f)) := by
  rw [range_inverse_comp_eq_orthogonal R P Q hPQ f hf]
  exact J.orthogonal_invariant hP

end OrthogonalComplexStructure

end Gaussian.Phase
