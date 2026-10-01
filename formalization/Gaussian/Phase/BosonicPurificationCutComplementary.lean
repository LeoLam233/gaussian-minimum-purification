import Gaussian.Phase.BosonicPurificationCuts
import Gaussian.Phase.BosonicPurificationComplementary

/-! Equal costs on the two actual sidewise cuts of a pure covariance. Both
physical and auxiliary complements are the original symplectic complements. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

/-- Actual sidewise cut costs agree across the complete symplectic bipartition,
including zero parties and unequal auxiliary side counts. -/
theorem auxiliaryCutCost_complementary (p : PureCompatibleCovariance (productForm Ω σ))
    (hΩa : Ω.IsAlt) (hσa : σ.IsAlt) (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (A : Submodule ℝ E) (S : Submodule ℝ F)
    (hA : (Ω.restrict A).Nondegenerate) (hS : (σ.restrict S).Nondegenerate) :
    p.auxiliaryCutCost A S = p.auxiliaryCutCost (Ω.orthogonal A) (σ.orthogonal S) := by
  let B := Ω.orthogonal A
  let T := σ.orthogonal S
  obtain ⟨hAc,hB⟩ := symplectic_complement_data Ω hΩa hΩn A hA
  obtain ⟨hSc,hT⟩ := symplectic_complement_data σ hσa hσn S hS
  let eA := Submodule.prodEquivOfIsCompl A B hAc
  let eS := Submodule.prodEquivOfIsCompl S T hSc
  let R := (LinearEquiv.prodProdProdComm ℝ A S B T).trans (eA.prodCongr eS)
  have hR (x : (A × S) × (B × T)) :
      R x = ((x.1.1 : E)+(x.2.1 : E),(x.1.2 : F)+(x.2.2 : F)) := rfl
  have hform : (productForm Ω σ).compl₁₂ R.toLinearMap R.toLinearMap =
      productForm (productForm (Ω.restrict A) (σ.restrict S))
        (productForm (Ω.restrict B) (σ.restrict T)) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change productForm Ω σ (R x) (R y) = _
    rw [hR,hR]
    have h₁ : Ω x.1.1 y.2.1 = 0 := y.2.1.property x.1.1 x.1.1.property
    have h₂ : Ω x.2.1 y.1.1 = 0 := hΩa.isRefl _ _ (x.2.1.property y.1.1 y.1.1.property)
    have h₃ : σ x.1.2 y.2.2 = 0 := y.2.2.property x.1.2 x.1.2.property
    have h₄ : σ x.2.2 y.1.2 = 0 := hσa.isRefl _ _ (x.2.2.property y.1.2 y.1.2.property)
    simp only [productForm_apply,map_add,LinearMap.add_apply,h₁,h₂,h₃,h₄,add_zero,zero_add]
    change Ω x.1.1 y.1.1 + Ω x.2.1 y.2.1 + (σ x.1.2 y.1.2 + σ x.2.2 y.2.2) =
      (Ω x.1.1 y.1.1 + σ x.1.2 y.1.2) + (Ω x.2.1 y.2.1 + σ x.2.2 y.2.2)
    ring
  let q := (p.pullback R).of_form_eq hform
  have hl : q.leftCovariance = p.auxiliaryCutCovariance A S := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change q.form (x,0) (y,0) = p.form (x.1,x.2) (y.1,y.2)
    dsimp only [q]
    rw [of_form_eq_form,pullback_form,hR,hR]
    simp
  have hr : q.rightCovariance = p.auxiliaryCutCovariance B T := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change q.form (0,x) (0,y) = p.form (x.1,x.2) (y.1,y.2)
    dsimp only [q]
    rw [of_form_eq_form,pullback_form,hR,hR]
    simp
  have h := q.complementary_formCost
    (productForm_alternating (fun x => hΩa x) (fun x => hσa x))
    (productForm_alternating (fun x => hΩa x) (fun x => hσa x))
    (productForm_nondegenerate hA hS) (productForm_nondegenerate hB hT)
    (Module.finBasis ℝ (A × S)) (Module.finBasis ℝ (B × T))
  have hcl := bosonFormCost_congr_forms (Module.finBasis ℝ (A × S))
    (V₁ := q.leftCovariance) (V₂ := p.auxiliaryCutCovariance A S)
    (Ω₁ := productForm (Ω.restrict A) (σ.restrict S))
    (Ω₂ := productForm (Ω.restrict A) (σ.restrict S))
    q.leftCovariance_symmetric (p.auxiliaryCutCovariance_symmetric A S)
    (productForm_alternating (fun x => hΩa x) (fun x => hσa x))
    (p.auxiliaryCutForm_alternating A S) hl rfl
  have hcr := bosonFormCost_congr_forms (Module.finBasis ℝ (B × T))
    (V₁ := q.rightCovariance) (V₂ := p.auxiliaryCutCovariance B T)
    (Ω₁ := productForm (Ω.restrict B) (σ.restrict T))
    (Ω₂ := productForm (Ω.restrict B) (σ.restrict T))
    q.rightCovariance_symmetric (p.auxiliaryCutCovariance_symmetric B T)
    (productForm_alternating (fun x => hΩa x) (fun x => hσa x))
    (p.auxiliaryCutForm_alternating B T) hr rfl
  exact hcl.symm.trans (h.trans hcr)

end PureCompatibleCovariance
end Gaussian.Phase
