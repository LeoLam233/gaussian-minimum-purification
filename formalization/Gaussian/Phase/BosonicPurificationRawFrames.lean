import Gaussian.Phase.BosonicPurificationSymplectic

/-! Finite raw real modules admit independently chosen positive coordinate
metrics. These are used only to construct symplectic equivalences; no common
Euclidean metric or covariance compatibility is assumed in the result. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

/-- A positive coordinate metric constructed on every finite real module. -/
@[instance_reducible] def finiteCoordinateInnerCore (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] : InnerProductSpace.Core ℝ E := by
  let L : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (finrank ℝ E))).toLinearEquiv.symm
  let B := (innerₗ (EuclideanSpace ℝ (Fin (finrank ℝ E)))).compl₁₂ L.toLinearMap L.toLinearMap
  apply covarianceInnerCore B
  · exact ⟨fun x y => (real_inner_comm (L x) (L y)).symm⟩
  · intro x hx
    change 0 < ⟪L x,L x⟫
    apply real_inner_self_pos.mpr
    intro h
    exact hx (L.injective (h.trans L.map_zero.symm))

/-- Equal-dimensional finite raw nondegenerate alternating spaces are genuinely
symplectically equivalent, with every auxiliary metric constructed internally. -/
theorem exists_raw_symplectic_equiv
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hΩa : Ω.IsAlt) (hσa : σ.IsAlt) (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hd : finrank ℝ E = finrank ℝ F) :
    ∃ L : E ≃ₗ[ℝ] F, ∀ x y, σ (L x) (L y) = Ω x y := by
  letI : NormedAddCommGroup E := (finiteCoordinateInnerCore E).toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore (finiteCoordinateInnerCore E).toCore
  letI : NormedAddCommGroup F := (finiteCoordinateInnerCore F).toNormedAddCommGroup
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore (finiteCoordinateInnerCore F).toCore
  exact exists_symplectic_equiv_of_finrank_eq Ω σ hΩa hσa hΩn hσn hd

end Gaussian.Phase
