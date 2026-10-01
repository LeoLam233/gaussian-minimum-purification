import Gaussian.Phase.BosonicPurificationBasisFrames
import Gaussian.Phase.ProtectedFrameSelection

/-! Actual real auxiliary subspaces are represented by complete orthonormal
frames, and the compact matrix embedding has the literal protected/auxiliary
product action. No optimization subspace is excluded by this parametrization. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every finite real subspace has an actual spanning orthonormal frame. -/
theorem exists_orthonormal_frame_spanning (S : Submodule ℝ F) {k : ℕ} (hk : finrank ℝ S=k) :
    ∃ v : Fin k → F, Orthonormal ℝ v ∧ Submodule.span ℝ (Set.range v) = S := by
  let b := (stdOrthonormalBasis ℝ S).reindex (finCongr hk)
  let v : Fin k → F := fun i => b i
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    exact b.inner_eq_ite i j
  refine ⟨v,hv,?_⟩
  have h := congrArg (fun U : Submodule ℝ S => U.map S.subtype) b.toBasis.span_eq
  simpa only [Submodule.map_span,← Set.range_comp,Submodule.map_top,Submodule.range_subtype,
    OrthonormalBasis.coe_toBasis,Function.comp_def,Submodule.subtype_apply,v] using h

def frameLinearMap {k : ℕ} (v : Fin k → F) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] F :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.constr ℝ v

@[simp] theorem frameLinearMap_basis {k : ℕ} (v : Fin k → F) (i : Fin k) :
    frameLinearMap v (EuclideanSpace.basisFun (Fin k) ℝ i) = v i := by
  exact Basis.constr_basis _ _ _ _

theorem frameLinearMap_range {k : ℕ} (v : Fin k → F) :
    (frameLinearMap v).range = Submodule.span ℝ (Set.range v) :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.constr_range ℝ

def frameRangeEquiv {k : ℕ} (v : Fin k → F) (hv : Orthonormal ℝ v) :
    EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] Submodule.span ℝ (Set.range v) :=
  (LinearEquiv.ofInjective (frameLinearMap v) (orthonormalFrameIsometry v hv).injective).trans
    (LinearEquiv.ofEq _ _ (frameLinearMap_range v))

@[simp] theorem frameRangeEquiv_apply {k : ℕ} (v : Fin k → F) (hv : Orthonormal ℝ v)
    (x : EuclideanSpace ℝ (Fin k)) : (frameRangeEquiv v hv x : F) = frameLinearMap v x := by
  rfl

def coordinateFrame {M k : ℕ} (b : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : Fin k → F := fun i => b.repr.symm (v i)

theorem coordinateFrame_orthonormal {M k : ℕ} (b : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (coordinateFrame b v) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  rw [coordinateFrame,coordinateFrame,b.repr.symm.inner_map_map]
  exact hv i j

/-- Any actual subspace appears among the coordinate frames used by compact attainment. -/
theorem exists_coordinateFrame_spanning {M k : ℕ} (b : OrthonormalBasis (Fin M) ℝ F)
    (S : Submodule ℝ F) (hk : finrank ℝ S=k) :
    ∃ v : Fin k → EuclideanSpace ℝ (Fin M), Orthonormal ℝ v ∧
      Submodule.span ℝ (Set.range (coordinateFrame b v)) = S := by
  obtain ⟨w,hw,hs⟩ := exists_orthonormal_frame_spanning S hk
  let v : Fin k → EuclideanSpace ℝ (Fin M) := fun i => b.repr (w i)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite] at hw ⊢
    intro i j
    change ⟪b.repr (w i),b.repr (w j)⟫ = _
    rw [b.repr.inner_map_map]
    exact hw i j
  refine ⟨v,hv,?_⟩
  have he : coordinateFrame b v = w := by funext i; exact b.repr.symm_apply_apply (w i)
  rw [he,hs]

section ProductFrame
variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
  {a M k : ℕ}

/-- The actual product action behind the compact coefficient matrix: physical
identity and the synthesized real auxiliary frame. -/
theorem basisReferenceFrameEmbedding_prod (bA : Basis (Fin a) ℝ A)
    (bF : OrthonormalBasis (Fin M) ℝ F) (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    basisReferenceFrameEmbedding (bA.prod bF.toBasis)
      (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v =
      (LinearMap.id : A →ₗ[ℝ] A).prodMap (frameLinearMap (coordinateFrame bF v)) := by
  apply (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).ext
  intro i
  cases i with
  | inl i =>
    rw [basisReferenceFrameEmbedding_physical]
    simp [Basis.prod_apply]
  | inr i =>
    rw [basisReferenceFrameEmbedding_auxiliary]
    simp only [Basis.prod_apply,Sum.elim_inr,Function.comp_apply,LinearMap.inr_apply,
      LinearMap.prodMap_apply,LinearMap.id_apply,OrthonormalBasis.coe_toBasis,frameLinearMap_basis]
    apply Prod.ext
    · change (LinearMap.fst ℝ A F) (∑ j, (v i) j • ((0,bF j) : A × F)) = 0
      rw [map_sum]
      simp
    · change (LinearMap.snd ℝ A F) (∑ j, (v i) j • ((0,bF j) : A × F)) = bF.repr.symm (v i)
      rw [map_sum]
      simpa only [map_smul,LinearMap.snd_apply] using bF.sum_repr_symm (v i)

end ProductFrame
end Gaussian.Phase
