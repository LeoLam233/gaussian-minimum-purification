import Gaussian.Phase.BosonicPurificationFrameGeometry
import Gaussian.Phase.BosonicPurificationCuts
import Gaussian.Phase.BosonicPurificationProductSubspaces

/-! The compact real-frame objective is the actual protected/auxiliary cut
cost on its full span. Nondegeneracy and real dimension are proved for those
spans; no fixed-frame or fixed-metric restriction is inserted into the domain. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def physicalAuxEmbedding (A : Submodule ℝ E) : (A × F) →ₗ[ℝ] (E × F) :=
  A.subtype.prodMap (LinearMap.id : F →ₗ[ℝ] F)

theorem physicalAuxEmbedding_injective (A : Submodule ℝ E) :
    Function.Injective (physicalAuxEmbedding (F := F) A) := by
  intro x y h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h)
  · exact congrArg (fun z : E × F => z.2) h

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

def physicalAuxCovariance (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) : LinearMap.BilinForm ℝ (A × F) :=
  p.form.compl₁₂ (physicalAuxEmbedding A) (physicalAuxEmbedding A)

theorem physicalAuxCovariance_symmetric (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) : (p.physicalAuxCovariance A).IsSymm :=
  ⟨fun x y => p.symmetric.eq (physicalAuxEmbedding A x) (physicalAuxEmbedding A y)⟩

theorem physicalAuxForm_alternating (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) : (productForm (Ω.restrict A) σ).IsAlt :=
  fun x => p.commutator_alternating (physicalAuxEmbedding A x)

theorem physicalAuxCovariance_positive (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (x : A × F) (hx : x≠0) : 0 < p.physicalAuxCovariance A x x := by
  change 0 < p.form (physicalAuxEmbedding A x) (physicalAuxEmbedding A x)
  apply p.positive
  intro h
  exact hx (physicalAuxEmbedding_injective A
    (h.trans (physicalAuxEmbedding (F := F) A).map_zero.symm))

/-- Exact comparison between the matrix frame embedding and the actual product
inclusion into the protected party and the selected auxiliary span. -/
theorem frame_cut_embedding {a M k : ℕ}
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (bA : Basis (Fin a) ℝ A) (bF : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) (hv : Orthonormal ℝ v)
    (x : A × EuclideanSpace ℝ (Fin k)) :
    physicalAuxEmbedding A (basisReferenceFrameEmbedding (bA.prod bF.toBasis)
      (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v x) =
    auxiliaryCutMap A (Submodule.span ℝ (Set.range (coordinateFrame bF v)))
      (((LinearEquiv.refl ℝ A).prodCongr
        (frameRangeEquiv (coordinateFrame bF v) (coordinateFrame_orthonormal bF v hv))) x) := by
  rw [basisReferenceFrameEmbedding_prod]
  change ((x.1 : E),frameLinearMap (coordinateFrame bF v) x.2) =
    ((x.1 : E),(frameRangeEquiv (coordinateFrame bF v)
      (coordinateFrame_orthonormal bF v hv) x.2 : F))
  rw [frameRangeEquiv_apply]

/-- The true pulled-back alternating form is nondegenerate exactly when the
actual selected auxiliary span is nondegenerate. -/
theorem basisReferenceFrame_span_nondegenerate_iff {a M k : ℕ}
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (bA : Basis (Fin a) ℝ A) (bF : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) (hv : Orthonormal ℝ v)
    (hA : (Ω.restrict A).Nondegenerate) :
    ((productForm (Ω.restrict A) σ).compl₁₂
      (basisReferenceFrameEmbedding (bA.prod bF.toBasis)
        (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v)
      (basisReferenceFrameEmbedding (bA.prod bF.toBasis)
        (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v)).Nondegenerate ↔
      (σ.restrict (Submodule.span ℝ (Set.range (coordinateFrame bF v)))).Nondegenerate := by
  let S := Submodule.span ℝ (Set.range (coordinateFrame bF v))
  let L := (LinearEquiv.refl ℝ A).prodCongr
    (frameRangeEquiv (coordinateFrame bF v) (coordinateFrame_orthonormal bF v hv))
  have he : (productForm (Ω.restrict A) σ).compl₁₂
      (basisReferenceFrameEmbedding (bA.prod bF.toBasis)
        (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v)
      (basisReferenceFrameEmbedding (bA.prod bF.toBasis)
        (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) v) =
      (productForm (Ω.restrict A) (σ.restrict S)).compl₁₂ L.toLinearMap L.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [basisReferenceFrameEmbedding_prod]
    change Ω x.1 y.1 + σ (frameLinearMap (coordinateFrame bF v) x.2)
      (frameLinearMap (coordinateFrame bF v) y.2) =
      Ω x.1 y.1 + σ (frameRangeEquiv (coordinateFrame bF v)
        (coordinateFrame_orthonormal bF v hv) x.2)
        (frameRangeEquiv (coordinateFrame bF v) (coordinateFrame_orthonormal bF v hv) y.2)
    rw [frameRangeEquiv_apply,frameRangeEquiv_apply]
  rw [he,form_nondegenerate_pullback_iff,productForm_nondegenerate_iff]
  exact and_iff_right hA

/-- The span represents all k real frame directions, including k=0. -/
theorem coordinateFrame_span_finrank {M k : ℕ} (bF : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) (hv : Orthonormal ℝ v) :
    finrank ℝ (Submodule.span ℝ (Set.range (coordinateFrame bF v))) = k := by
  rw [← (frameRangeEquiv (coordinateFrame bF v)
    (coordinateFrame_orthonormal bF v hv)).finrank_eq]
  simp

/-- The matrix objective on an actual orthonormal frame is exactly the
basis-independent two-form cost of its actual auxiliary span. -/
theorem basisReferenceFrameCost_eq_auxiliaryCutCost {a M k : ℕ}
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (bA : Basis (Fin a) ℝ A) (bF : OrthonormalBasis (Fin M) ℝ F)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) (hv : Orthonormal ℝ v)
    (hA : (Ω.restrict A).Nondegenerate)
    (hS : (σ.restrict (Submodule.span ℝ (Set.range (coordinateFrame bF v)))).Nondegenerate) :
    basisReferenceFrameCost (bA.prod bF.toBasis) (bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
      (p.physicalAuxCovariance A) (productForm (Ω.restrict A) σ)
      (p.physicalAuxCovariance_symmetric A) (p.physicalAuxForm_alternating A) v =
      p.auxiliaryCutCost A (Submodule.span ℝ (Set.range (coordinateFrame bF v))) := by
  let S := Submodule.span ℝ (Set.range (coordinateFrame bF v))
  let L := (LinearEquiv.refl ℝ A).prodCongr
    (frameRangeEquiv (coordinateFrame bF v) (coordinateFrame_orthonormal bF v hv))
  let e := bA.prod bF.toBasis
  let b := bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f := basisReferenceFrameEmbedding e b v
  have he (x : A × EuclideanSpace ℝ (Fin k)) :
      physicalAuxEmbedding A (f x) = auxiliaryCutMap A S (L x) :=
    p.frame_cut_embedding A bA bF v hv x
  have hV : (p.auxiliaryCutCovariance A S).compl₁₂ L.toLinearMap L.toLinearMap =
      (p.physicalAuxCovariance A).compl₁₂ f f := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change p.form (auxiliaryCutMap A S (L x)) (auxiliaryCutMap A S (L y)) =
      p.form (physicalAuxEmbedding A (f x)) (physicalAuxEmbedding A (f y))
    rw [he,he]
  have hΩ : (productForm (Ω.restrict A) (σ.restrict S)).compl₁₂ L.toLinearMap L.toLinearMap =
      (productForm (Ω.restrict A) σ).compl₁₂ f f := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change productForm Ω σ (auxiliaryCutMap A S (L x)) (auxiliaryCutMap A S (L y)) =
      productForm Ω σ (physicalAuxEmbedding A (f x)) (physicalAuxEmbedding A (f y))
    rw [he,he]
  have h := bosonFormCost_pullback_general (p.auxiliaryCutCovariance A S)
    (productForm (Ω.restrict A) (σ.restrict S)) (p.auxiliaryCutCovariance_symmetric A S)
    (p.auxiliaryCutForm_alternating A S) (productForm_nondegenerate hA hS)
    (p.auxiliaryCut_uncertainty A S) L (Module.finBasis ℝ (A × S)) b
  have hc := bosonFormCost_congr_forms b
    (V₁ := (p.physicalAuxCovariance A).compl₁₂ f f)
    (V₂ := (p.auxiliaryCutCovariance A S).compl₁₂ L.toLinearMap L.toLinearMap)
    (Ω₁ := (productForm (Ω.restrict A) σ).compl₁₂ f f)
    (Ω₂ := (productForm (Ω.restrict A) (σ.restrict S)).compl₁₂ L.toLinearMap L.toLinearMap)
    ⟨fun x y => (p.physicalAuxCovariance_symmetric A).eq (f x) (f y)⟩
    ⟨fun x y => (p.auxiliaryCutCovariance_symmetric A S).eq (L x) (L y)⟩
    (fun x => p.physicalAuxForm_alternating A (f x)) (fun x => p.auxiliaryCutForm_alternating A S (L x))
    hV.symm hΩ.symm
  exact hc.trans h

end PureCompatibleCovariance
end Gaussian.Phase
