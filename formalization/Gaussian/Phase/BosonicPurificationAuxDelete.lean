import Gaussian.Phase.BosonicPurificationProductSubspaces
import Gaussian.Phase.BosonicPurificationLift
import Gaussian.Phase.BosonicPurificationCuts

/-! Genuine deletion of an invariant auxiliary pure factor. The smaller
covariance lives on the actual symplectic complement, preserves all physical
coefficients, and preserves any retained cut contained in that complement. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

/-- Invariance under a pure symplectic generator passes to the true complement. -/
theorem symplectic_orthogonal_invariant {H : Type*} [AddCommGroup H] [Module ℝ H]
    {τ : LinearMap.BilinForm ℝ H} (p : PureCompatibleCovariance τ)
    (P : Submodule ℝ H) (hP : ∀ x ∈ P, p.generator x ∈ P) :
    ∀ x ∈ τ.orthogonal P, p.generator x ∈ τ.orthogonal P := by
  intro x hx y hy
  have h := p.symplectic (p.generator y) x
  rw [p.square_neg,map_neg,LinearMap.neg_apply] at h
  have hz := hx (p.generator y) (hP y hy)
  linarith

/-- Delete a genuinely invariant auxiliary factor using its true symplectic complement. -/
def deleteAuxiliary (p : PureCompatibleCovariance (productForm Ω σ))
    (P : Submodule ℝ F)
    (hInv : ∀ x ∈ P.map (LinearMap.inr ℝ E F),
      p.generator x ∈ P.map (LinearMap.inr ℝ E F)) :
    PureCompatibleCovariance (productForm Ω (σ.restrict (σ.orthogonal P))) := by
  let U := (productForm Ω σ).orthogonal (P.map (LinearMap.inr ℝ E F))
  have hU : U=(⊤ : Submodule ℝ E).prod (σ.orthogonal P) :=
    productForm_orthogonal_auxiliary Ω σ P
  let L := (fullProductSubspaceEquiv (E := E) (σ.orthogonal P)).trans
    (LinearEquiv.ofEq _ _ hU.symm)
  let q := p.restrict U (p.symplectic_orthogonal_invariant _ hInv)
  exact (q.pullback L).of_form_eq (by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl)

@[simp] theorem deleteAuxiliary_form (p : PureCompatibleCovariance (productForm Ω σ))
    (P : Submodule ℝ F)
    (hInv : ∀ x ∈ P.map (LinearMap.inr ℝ E F),
      p.generator x ∈ P.map (LinearMap.inr ℝ E F)) (x y : E × σ.orthogonal P) :
    (p.deleteAuxiliary P hInv).form x y = p.form (x.1,(x.2 : F)) (y.1,(y.2 : F)) := by
  rw [deleteAuxiliary,of_form_eq_form,pullback_form]
  rfl

@[simp] theorem deleteAuxiliary_physical (p : PureCompatibleCovariance (productForm Ω σ))
    (P : Submodule ℝ F)
    (hInv : ∀ x ∈ P.map (LinearMap.inr ℝ E F),
      p.generator x ∈ P.map (LinearMap.inr ℝ E F)) (x y : E) :
    (p.deleteAuxiliary P hInv).form (x,0) (y,0) = p.form (x,0) (y,0) := by simp

/-- An actual pure covariance found inside a mixed cut makes its ambient
auxiliary image invariant under the global pure generator. -/
theorem invariant_auxiliary_of_subcut_pure
    (p : PureCompatibleCovariance (productForm Ω σ)) (S : Submodule ℝ F) (T : Submodule ℝ S)
    (q : PureCompatibleCovariance ((σ.restrict S).restrict T))
    (hq : ∀ x y : T, q.form x y = p.form (0,(x : S)) (0,(y : S))) :
    ∀ x ∈ (T.map S.subtype).map (LinearMap.inr ℝ E F),
      p.generator x ∈ (T.map S.subtype).map (LinearMap.inr ℝ E F) := by
  let f : T →ₗ[ℝ] (E × F) := (LinearMap.inr ℝ E F).comp (S.subtype.comp T.subtype)
  have hf : Function.Injective f :=
    (LinearMap.inr_injective (R := ℝ) (M := E) (M₂ := F)).comp (S.subtype_injective.comp T.subtype_injective)
  have h := p.invariant_range_of_pure_embedding q f hf
    (fun x y => by simp [f]) (fun x y => (hq x y).symm)
  simpa only [f,LinearMap.range_comp,Submodule.range_subtype] using h

/-- A retained actual subspace remains nondegenerate in the smaller auxiliary carrier. -/
theorem deleteAuxiliary_split_nondegenerate (P W : Submodule ℝ F)
    (hWP : W ≤ σ.orthogonal P) (hW : (σ.restrict W).Nondegenerate) :
    ((σ.restrict (σ.orthogonal P)).restrict (W.comap (σ.orthogonal P).subtype)).Nondegenerate := by
  apply nondegenerate_of_form_equiv (σ.restrict W) _ hW
    (Submodule.comapSubtypeEquivOfLe hWP).symm
  intro x y
  rfl

/-- Deleting an invariant auxiliary factor preserves the actual cost of each
cut in its complement; the smaller split is the literal subtype pullback. -/
theorem deleteAuxiliary_cost (p : PureCompatibleCovariance (productForm Ω σ))
    (P W : Submodule ℝ F)
    (hInv : ∀ x ∈ P.map (LinearMap.inr ℝ E F),
      p.generator x ∈ P.map (LinearMap.inr ℝ E F))
    (hWP : W ≤ σ.orthogonal P) (A : Submodule ℝ E)
    (hA : (Ω.restrict A).Nondegenerate) (hW : (σ.restrict W).Nondegenerate) :
    (p.deleteAuxiliary P hInv).auxiliaryCutCost A (W.comap (σ.orthogonal P).subtype) =
      p.auxiliaryCutCost A W := by
  let T := W.comap (σ.orthogonal P).subtype
  let L := (LinearEquiv.refl ℝ A).prodCongr (Submodule.comapSubtypeEquivOfLe hWP)
  have h := bosonFormCost_pullback_general (p.auxiliaryCutCovariance A W)
    (productForm (Ω.restrict A) (σ.restrict W)) (p.auxiliaryCutCovariance_symmetric A W)
    (p.auxiliaryCutForm_alternating A W) (productForm_nondegenerate hA hW)
    (p.auxiliaryCut_uncertainty A W) L (Module.finBasis ℝ (A × W)) (Module.finBasis ℝ (A × T))
  have hV : (p.auxiliaryCutCovariance A W).compl₁₂ L.toLinearMap L.toLinearMap =
      (p.deleteAuxiliary P hInv).auxiliaryCutCovariance A T := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (p.deleteAuxiliary_form P hInv (x.1,x.2) (y.1,y.2)).symm
  have hΩ : (productForm (Ω.restrict A) (σ.restrict W)).compl₁₂ L.toLinearMap L.toLinearMap =
      productForm (Ω.restrict A) ((σ.restrict (σ.orthogonal P)).restrict T) := rfl
  have hc := bosonFormCost_congr_forms (Module.finBasis ℝ (A × T))
    (V₁ := (p.auxiliaryCutCovariance A W).compl₁₂ L.toLinearMap L.toLinearMap)
    (V₂ := (p.deleteAuxiliary P hInv).auxiliaryCutCovariance A T)
    (Ω₁ := (productForm (Ω.restrict A) (σ.restrict W)).compl₁₂ L.toLinearMap L.toLinearMap)
    (Ω₂ := productForm (Ω.restrict A) ((σ.restrict (σ.orthogonal P)).restrict T))
    ⟨fun x y => (p.auxiliaryCutCovariance_symmetric A W).eq (L x) (L y)⟩
    ((p.deleteAuxiliary P hInv).auxiliaryCutCovariance_symmetric A T)
    (fun x => p.auxiliaryCutForm_alternating A W (L x))
    ((p.deleteAuxiliary P hInv).auxiliaryCutForm_alternating A T) hV hΩ
  exact hc.symm.trans h

end PureCompatibleCovariance
end Gaussian.Phase
