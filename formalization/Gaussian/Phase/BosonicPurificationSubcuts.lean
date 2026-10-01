import Gaussian.Phase.BosonicPurificationProductSelection
import Gaussian.Phase.BosonicPurificationCuts

/-! Exact actual auxiliary subcut transports. Nested subtype coordinates are
identified with their actual ambient images, preserving both forms and cost. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

theorem auxiliary_subcut_nondegenerate (S : Submodule ℝ F) (T : Submodule ℝ S)
    (hT : ((σ.restrict S).restrict T).Nondegenerate) :
    (σ.restrict (T.map S.subtype)).Nondegenerate := by
  exact nondegenerate_of_form_equiv ((σ.restrict S).restrict T)
    (σ.restrict (T.map S.subtype)) hT (Submodule.equivSubtypeMap S T) (fun x y => rfl)

/-- A nested auxiliary restriction has the cost of its genuine ambient image. -/
theorem auxiliary_subcut_cost (p : PureCompatibleCovariance (productForm Ω σ))
    (hΩa : Ω.IsAlt) (hσa : σ.IsAlt) (A : Submodule ℝ E) (S : Submodule ℝ F)
    (T : Submodule ℝ S) (hA : (Ω.restrict A).Nondegenerate)
    (hT : ((σ.restrict S).restrict T).Nondegenerate) :
    productRestrictionCost (p.auxiliaryCutCovariance A S) (Ω.restrict A) (σ.restrict S)
      (p.auxiliaryCutCovariance_symmetric A S) (fun x => hΩa x) (fun x => hσa x) T =
      p.auxiliaryCutCost A (T.map S.subtype) := by
  let W := T.map S.subtype
  let L := (LinearEquiv.refl ℝ A).prodCongr (Submodule.equivSubtypeMap S T)
  have hW : (σ.restrict W).Nondegenerate := auxiliary_subcut_nondegenerate S T hT
  have h := bosonFormCost_pullback_general (p.auxiliaryCutCovariance A W)
    (productForm (Ω.restrict A) (σ.restrict W)) (p.auxiliaryCutCovariance_symmetric A W)
    (p.auxiliaryCutForm_alternating A W) (productForm_nondegenerate hA hW)
    (p.auxiliaryCut_uncertainty A W) L (Module.finBasis ℝ (A × W)) (Module.finBasis ℝ (A × T))
  exact h

/-- Selecting an excess-side plane gives a genuine smaller auxiliary split on
the same full pure covariance, with lower cost and an explicit equality-pure
plane inside the old split. -/
theorem exists_auxiliary_subcut_selection (p : PureCompatibleCovariance (productForm Ω σ))
    (hΩa : Ω.IsAlt) (hσa : σ.IsAlt) (A : Submodule ℝ E) (S : Submodule ℝ F)
    (hA : (Ω.restrict A).Nondegenerate) (hS : (σ.restrict S).Nondegenerate)
    (hExcess : finrank ℝ A < finrank ℝ S) :
    ∃ P : Submodule ℝ S, finrank ℝ P=2 ∧ ((σ.restrict S).restrict P).Nondegenerate ∧
      ((σ.restrict S).restrict ((σ.restrict S).orthogonal P)).Nondegenerate ∧
      IsCompl P ((σ.restrict S).orthogonal P) ∧
      finrank ℝ ((σ.restrict S).orthogonal P) = finrank ℝ S-2 ∧
      p.auxiliaryCutCost A (((σ.restrict S).orthogonal P).map S.subtype) ≤ p.auxiliaryCutCost A S ∧
      (p.auxiliaryCutCost A (((σ.restrict S).orthogonal P).map S.subtype) = p.auxiliaryCutCost A S →
        ∃ q : PureCompatibleCovariance ((σ.restrict S).restrict P),
          ∀ x y : P, q.form x y = p.form (0,(x : S)) (0,(y : S))) := by
  obtain ⟨P,hPd,hPn,hWn,hPc,hWd,hcost,hpure⟩ := exists_bosonic_product_selection
    (p.auxiliaryCutCovariance A S) (Ω.restrict A) (σ.restrict S)
    (p.auxiliaryCutCovariance_symmetric A S) (fun x => hΩa x) (fun x => hσa x)
    hA hS (p.auxiliaryCut_uncertainty A S) hExcess
  have hc := p.auxiliary_subcut_cost hΩa hσa A S ((σ.restrict S).orthogonal P) hA hWn
  refine ⟨P,hPd,hPn,hWn,hPc,hWd,?_,?_⟩
  · exact hc.symm.trans_le hcost
  · intro heq
    obtain ⟨q,hq⟩ := hpure (hc.trans heq)
    exact ⟨q,fun x y => hq x y⟩

end PureCompatibleCovariance
end Gaussian.Phase
