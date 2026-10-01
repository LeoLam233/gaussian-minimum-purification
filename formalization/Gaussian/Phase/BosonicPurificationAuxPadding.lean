import Gaussian.Phase.BosonicPurificationDomain
import Gaussian.Phase.BosonicPurificationStandardLift

/-! Padding an actual raw covariance purifier by finite pure modes. The literal
physical restriction and selected-side cost are preserved, and the finite total
is the actual auxiliary dimension. No padding property is a domain field. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}

/-- Put an actual pure product into the auxiliary factor, preserving the first coordinate. -/
def padAuxiliary (p : PureCompatibleCovariance (productForm Ω σ)) (r : PureCompatibleCovariance τ) :
    PureCompatibleCovariance (productForm Ω (productForm σ τ)) :=
  ((p.prod r).pullback (LinearEquiv.prodAssoc ℝ E F G).symm).of_form_eq (by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (Ω x.1 y.1 + σ x.2.1 y.2.1) + τ x.2.2 y.2.2 =
      Ω x.1 y.1 + (σ x.2.1 y.2.1 + τ x.2.2 y.2.2)
    exact add_assoc _ _ _)

@[simp] theorem padAuxiliary_form (p : PureCompatibleCovariance (productForm Ω σ))
    (r : PureCompatibleCovariance τ) (x y : E × (F × G)) :
    (p.padAuxiliary r).form x y = p.form (x.1,x.2.1) (y.1,y.2.1) + r.form x.2.2 y.2.2 := by
  rw [padAuxiliary,of_form_eq_form,pullback_form]
  rfl

@[simp] theorem padAuxiliary_physical (p : PureCompatibleCovariance (productForm Ω σ))
    (r : PureCompatibleCovariance τ) (x y : E) :
    (p.padAuxiliary r).form (x,0) (y,0) = p.form (x,0) (y,0) := by simp

end PureCompatibleCovariance

/-- Include the old selected auxiliary subspace and put every added mode on the other side. -/
def paddedSplitEmbedding (S : Submodule ℝ F) : S →ₗ[ℝ] (F × G) :=
  S.subtype.prod (0 : S →ₗ[ℝ] G)

def paddedSplit (S : Submodule ℝ F) : Submodule ℝ (F × G) :=
  (paddedSplitEmbedding (G := G) S).range

theorem paddedSplitEmbedding_injective (S : Submodule ℝ F) :
    Function.Injective (paddedSplitEmbedding (G := G) S) := by
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

def paddedSplitEquiv (S : Submodule ℝ F) : S ≃ₗ[ℝ] paddedSplit (G := G) S :=
  LinearEquiv.ofInjective (paddedSplitEmbedding S) (paddedSplitEmbedding_injective S)

@[simp] theorem paddedSplitEquiv_apply (S : Submodule ℝ F) (x : S) :
    (paddedSplitEquiv (G := G) S x : F × G) = ((x : F),0) := rfl

theorem paddedSplit_finrank (S : Submodule ℝ F) :
    finrank ℝ (paddedSplit (G := G) S) = finrank ℝ S := (paddedSplitEquiv S).finrank_eq.symm

theorem paddedSplit_nondegenerate (σ : LinearMap.BilinForm ℝ F) (τ : LinearMap.BilinForm ℝ G)
    (S : Submodule ℝ F) (hS : (σ.restrict S).Nondegenerate) :
    ((productForm σ τ).restrict (paddedSplit (G := G) S)).Nondegenerate := by
  apply symplectic_range_nondegenerate (σ.restrict S) (productForm σ τ) hS (paddedSplitEmbedding S)
  intro x y
  simp [paddedSplitEmbedding]

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}

/-- Exact selected-side covariance cost preservation under actual auxiliary padding. -/
theorem padAuxiliary_cost (p : PureCompatibleCovariance (productForm Ω σ))
    (r : PureCompatibleCovariance τ) (A : Submodule ℝ E) (S : Submodule ℝ F)
    (hA : (Ω.restrict A).Nondegenerate) (hS : (σ.restrict S).Nondegenerate) :
    (p.padAuxiliary r).auxiliaryCutCost A (paddedSplit (G := G) S) = p.auxiliaryCutCost A S := by
  let T := paddedSplit (G := G) S
  let q := p.padAuxiliary r
  let L := (LinearEquiv.refl ℝ A).prodCongr (paddedSplitEquiv (G := G) S)
  have hV : (q.auxiliaryCutCovariance A T).compl₁₂ L.toLinearMap L.toLinearMap =
      p.auxiliaryCutCovariance A S := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (p.padAuxiliary r).form (x.1,(x.2,0)) (y.1,(y.2,0)) = p.form (x.1,x.2) (y.1,y.2)
    simp
  have hΩ : (productForm (Ω.restrict A) ((productForm σ τ).restrict T)).compl₁₂
      L.toLinearMap L.toLinearMap = productForm (Ω.restrict A) (σ.restrict S) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.1 y.1 + (σ x.2 y.2 + τ 0 0) = Ω x.1 y.1 + σ x.2 y.2
    simp
  have h := bosonFormCost_pullback_general (q.auxiliaryCutCovariance A T)
    (productForm (Ω.restrict A) ((productForm σ τ).restrict T))
    (q.auxiliaryCutCovariance_symmetric A T) (q.auxiliaryCutForm_alternating A T)
    (productForm_nondegenerate hA (paddedSplit_nondegenerate σ τ S hS))
    (q.auxiliaryCut_uncertainty A T) L (Module.finBasis ℝ (A × T)) (Module.finBasis ℝ (A × S))
  have hc := bosonFormCost_congr_forms (Module.finBasis ℝ (A × S))
    (V₁ := (q.auxiliaryCutCovariance A T).compl₁₂ L.toLinearMap L.toLinearMap)
    (V₂ := p.auxiliaryCutCovariance A S)
    (Ω₁ := (productForm (Ω.restrict A) ((productForm σ τ).restrict T)).compl₁₂ L.toLinearMap L.toLinearMap)
    (Ω₂ := productForm (Ω.restrict A) (σ.restrict S))
    ⟨fun x y => (q.auxiliaryCutCovariance_symmetric A T).eq (L x) (L y)⟩
    (p.auxiliaryCutCovariance_symmetric A S)
    (fun x => q.auxiliaryCutForm_alternating A T (L x)) (p.auxiliaryCutForm_alternating A S) hV hΩ
  exact h.symm.trans hc

end PureCompatibleCovariance

namespace BosonicCovariancePurifier
variable {H : Type u} [AddCommGroup H] [Module ℝ H] [FiniteDimensional ℝ H]
  {V Ω : LinearMap.BilinForm ℝ H} {M N : ℕ}

/-- Pad a genuine domain point to any larger finite auxiliary total. -/
def pad (p : BosonicCovariancePurifier V Ω M) (hMN : M≤N) : BosonicCovariancePurifier V Ω N where
  Auxiliary := p.Auxiliary × StandardBosonicSpaceLift.{u} (N-M)
  commutator := productForm p.commutator (standardSymplecticFormLift (N-M))
  alternating := productForm_alternating p.alternating (standardPureCovarianceLift (N-M)).commutator_alternating
  nondegenerate := productForm_nondegenerate p.nondegenerate (standardPureCovarianceLift (N-M)).commutator_nondegenerate
  mode_count := by rw [Module.finrank_prod,p.mode_count,finrank_standardBosonicSpaceLift]; omega
  covariance := p.covariance.padAuxiliary (standardPureCovarianceLift (N-M))
  physical x y := by rw [PureCompatibleCovariance.padAuxiliary_physical,p.physical]
  split := paddedSplit p.split
  split_nondegenerate := paddedSplit_nondegenerate _ _ p.split p.split_nondegenerate

/-- The finite-total padding operation has exactly the original objective value. -/
theorem pad_cost (p : BosonicCovariancePurifier V Ω M) (hMN : M≤N)
    (A : Submodule ℝ H) (hA : (Ω.restrict A).Nondegenerate) :
    (p.pad hMN).cost A = p.cost A :=
  p.covariance.padAuxiliary_cost (standardPureCovarianceLift (N-M)) A p.split hA p.split_nondegenerate

/-- Adding modes to the opposite side preserves the actual selected-side count. -/
theorem pad_leftModes (p : BosonicCovariancePurifier V Ω M) (hMN : M≤N) :
    (p.pad hMN).leftModes = p.leftModes := by
  unfold leftModes
  change finrank ℝ (paddedSplit p.split) / 2 = finrank ℝ p.split / 2
  rw [paddedSplit_finrank]

end BosonicCovariancePurifier
end Gaussian.Phase
