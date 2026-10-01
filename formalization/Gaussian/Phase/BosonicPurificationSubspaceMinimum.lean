import Gaussian.Phase.BosonicPurificationFrameCuts

/-! Genuine compact attainment over all nondegenerate auxiliary subspaces of a
fixed real dimension. Every such subspace is represented by an orthonormal
frame, and the frame objective is the actual simultaneous two-form cut cost. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

/-- An actual fixed reference covariance has a minimum over every nonempty
fixed-dimensional symplectic cut class. No metric, frame, rank or compactness
hypothesis is imposed on the raw domain. -/
theorem exists_auxiliarySubspaceCost_minimum
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (hA : (Ω.restrict A).Nondegenerate) {k : ℕ}
    (S₀ : Submodule ℝ F) (hd₀ : finrank ℝ S₀ = k)
    (hnd₀ : (σ.restrict S₀).Nondegenerate) :
    ∃ S : Submodule ℝ F, finrank ℝ S=k ∧ (σ.restrict S).Nondegenerate ∧
      ∀ T : Submodule ℝ F, finrank ℝ T=k → (σ.restrict T).Nondegenerate →
        p.auxiliaryCutCost A S ≤ p.auxiliaryCutCost A T := by
  let core := finiteCoordinateInnerCore F
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore core.toCore
  let bA := Module.finBasis ℝ A
  let bF := stdOrthonormalBasis ℝ F
  let e := bA.prod bF.toBasis
  let b := bA.prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  obtain ⟨v₀,hv₀,hs₀⟩ := exists_coordinateFrame_spanning bF S₀ hd₀
  have hndv₀ := (p.basisReferenceFrame_span_nondegenerate_iff A bA bF v₀ hv₀ hA).mpr
    (by rw [hs₀]; exact hnd₀)
  obtain ⟨v,hv,hnd,hmin⟩ := exists_basisReferenceFrameCost_minimum e b
    (p.physicalAuxCovariance A) (productForm (Ω.restrict A) σ)
    (p.physicalAuxCovariance_symmetric A) (p.physicalAuxForm_alternating A)
    (p.physicalAuxCovariance_positive A) v₀ hv₀ hndv₀
  let S := Submodule.span ℝ (Set.range (coordinateFrame bF v))
  have hS : (σ.restrict S).Nondegenerate :=
    (p.basisReferenceFrame_span_nondegenerate_iff A bA bF v hv hA).mp hnd
  refine ⟨S,coordinateFrame_span_finrank bF v hv,hS,?_⟩
  intro T hT hndT
  obtain ⟨w,hw,hsw⟩ := exists_coordinateFrame_spanning bF T hT
  have hSw : (σ.restrict (Submodule.span ℝ (Set.range (coordinateFrame bF w)))).Nondegenerate := by
    rw [hsw]
    exact hndT
  have hc := hmin w hw ((p.basisReferenceFrame_span_nondegenerate_iff A bA bF w hw hA).mpr hSw)
  rw [p.basisReferenceFrameCost_eq_auxiliaryCutCost A bA bF v hv hA hS,
    p.basisReferenceFrameCost_eq_auxiliaryCutCost A bA bF w hw hA hSw,hsw] at hc
  exact hc

/-- A fixed reference covariance attains its minimum over all actual finite
nondegenerate auxiliary splits, with every possible side count included. -/
theorem exists_auxiliaryCutCost_minimum
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (hA : (Ω.restrict A).Nondegenerate) :
    ∃ S : Submodule ℝ F, (σ.restrict S).Nondegenerate ∧
      ∀ T : Submodule ℝ F, (σ.restrict T).Nondegenerate →
        p.auxiliaryCutCost A S ≤ p.auxiliaryCutCost A T := by
  classical
  have hm (k : Fin (finrank ℝ F+1)) : ∃ S : Submodule ℝ F,
      (σ.restrict S).Nondegenerate ∧
      ∀ T : Submodule ℝ F, finrank ℝ T=k.val → (σ.restrict T).Nondegenerate →
        p.auxiliaryCutCost A S ≤ p.auxiliaryCutCost A T := by
    by_cases hk : ∃ S : Submodule ℝ F, finrank ℝ S=k.val ∧ (σ.restrict S).Nondegenerate
    · obtain ⟨S₀,hd₀,hnd₀⟩ := hk
      obtain ⟨S,_,hS,hmin⟩ := p.exists_auxiliarySubspaceCost_minimum A hA S₀ hd₀ hnd₀
      exact ⟨S,hS,hmin⟩
    · refine ⟨⊥,⟨fun x _ => Subsingleton.elim x 0,fun x _ => Subsingleton.elim x 0⟩,?_⟩
      intro T hT hndT
      exact (hk ⟨T,hT,hndT⟩).elim
  choose S hS hmin using hm
  obtain ⟨j,_,hjmin⟩ := Set.exists_min_image (Set.univ : Set (Fin (finrank ℝ F+1)))
    (fun i => p.auxiliaryCutCost A (S i)) (Set.toFinite _) Set.univ_nonempty
  refine ⟨S j,hS j,?_⟩
  intro T hT
  let k : Fin (finrank ℝ F+1) := ⟨finrank ℝ T,by have h:=T.finrank_le; omega⟩
  exact (hjmin k (Set.mem_univ k)).trans (hmin k T rfl hT)

end PureCompatibleCovariance
end Gaussian.Phase
