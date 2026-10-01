import Gaussian.Phase.BosonicPurificationCanonicalSplit
import Gaussian.Phase.BosonicPurificationCrossOrbit
import Gaussian.Phase.BosonicPurificationCostCongruence

/-! Actual covariance cuts on a protected physical subspace and an auxiliary
symplectic split. The objective is the original two-form cost, and transport
through an auxiliary orbit is a proved theorem rather than a domain axiom. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

/-- The literal inclusion of a protected party and selected auxiliary subspace. -/
def auxiliaryCutMap (A : Submodule ℝ E) (S : Submodule ℝ F) :
    (A × S) →ₗ[ℝ] (E × F) := A.subtype.prodMap S.subtype

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}

def auxiliaryCutCovariance (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) : LinearMap.BilinForm ℝ (A × S) :=
  p.form.compl₁₂ (auxiliaryCutMap A S) (auxiliaryCutMap A S)

@[simp] theorem auxiliaryCutCovariance_apply (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) (x y : A × S) :
    p.auxiliaryCutCovariance A S x y = p.form (x.1,x.2) (y.1,y.2) := rfl

theorem auxiliaryCutCovariance_symmetric (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) : (p.auxiliaryCutCovariance A S).IsSymm :=
  ⟨fun x y => p.symmetric.eq (auxiliaryCutMap A S x) (auxiliaryCutMap A S y)⟩

theorem auxiliaryCutForm_alternating (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) :
    (productForm (Ω.restrict A) (σ.restrict S)).IsAlt :=
  fun x => p.commutator_alternating (auxiliaryCutMap A S x)

theorem auxiliaryCut_uncertainty (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) :
    Gaussian.Covariance.RealifiedUncertainty (p.auxiliaryCutCovariance A S)
      (productForm (Ω.restrict A) (σ.restrict S)) :=
  fun x y => p.uncertainty (auxiliaryCutMap A S x) (auxiliaryCutMap A S y)

/-- The independently defined covariance cost of this actual physical/auxiliary cut. -/
def auxiliaryCutCost (p : PureCompatibleCovariance (productForm Ω σ))
    (A : Submodule ℝ E) (S : Submodule ℝ F) : ℝ :=
  bosonFormCost (Module.finBasis ℝ (A × S)) (p.auxiliaryCutCovariance A S)
    (productForm (Ω.restrict A) (σ.restrict S))
    (p.auxiliaryCutCovariance_symmetric A S) (p.auxiliaryCutForm_alternating A S)

/-- The auxiliary orbit transports the cost of every actual nondegenerate cut,
including changes of auxiliary carrier and finite coefficient indexing. -/
theorem auxiliaryCutCost_transport
    (p : PureCompatibleCovariance (productForm Ω σ))
    (q : PureCompatibleCovariance (productForm Ω τ)) (Q : F ≃ₗ[ℝ] G)
    (hQ : ∀ x y, τ (Q x) (Q y) = σ x y)
    (hcov : ∀ a b x y, q.form (a,Q x) (b,Q y) = p.form (a,x) (b,y))
    (A : Submodule ℝ E) (S : Submodule ℝ F)
    (hA : (Ω.restrict A).Nondegenerate) (hS : (σ.restrict S).Nondegenerate) :
    p.auxiliaryCutCost A S = q.auxiliaryCutCost A (S.map Q.toLinearMap) := by
  let T := S.map Q.toLinearMap
  let L := (LinearEquiv.refl ℝ A).prodCongr (Q.submoduleMap S)
  have hT : (τ.restrict T).Nondegenerate :=
    nondegenerate_of_form_equiv (σ.restrict S) (τ.restrict T) hS (Q.submoduleMap S)
      (fun x y => hQ x y)
  have hVpull : (q.auxiliaryCutCovariance A T).compl₁₂ L.toLinearMap L.toLinearMap =
      p.auxiliaryCutCovariance A S := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change q.form (x.1,Q x.2) (y.1,Q y.2) = p.form (x.1,x.2) (y.1,y.2)
    exact hcov x.1 y.1 x.2 y.2
  have hΩpull : (productForm (Ω.restrict A) (τ.restrict T)).compl₁₂
      L.toLinearMap L.toLinearMap = productForm (Ω.restrict A) (σ.restrict S) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.1 y.1 + τ (Q x.2) (Q y.2) = Ω x.1 y.1 + σ x.2 y.2
    rw [hQ]
  have h := bosonFormCost_pullback_general (q.auxiliaryCutCovariance A T)
    (productForm (Ω.restrict A) (τ.restrict T)) (q.auxiliaryCutCovariance_symmetric A T)
    (q.auxiliaryCutForm_alternating A T) (productForm_nondegenerate hA hT)
    (q.auxiliaryCut_uncertainty A T) L (Module.finBasis ℝ (A × T))
    (Module.finBasis ℝ (A × S))
  have hc := bosonFormCost_congr_forms (Module.finBasis ℝ (A × S))
    (V₁ := p.auxiliaryCutCovariance A S)
    (V₂ := (q.auxiliaryCutCovariance A T).compl₁₂ L.toLinearMap L.toLinearMap)
    (Ω₁ := productForm (Ω.restrict A) (σ.restrict S))
    (Ω₂ := (productForm (Ω.restrict A) (τ.restrict T)).compl₁₂ L.toLinearMap L.toLinearMap)
    (p.auxiliaryCutCovariance_symmetric A S)
    ⟨fun x y => (q.auxiliaryCutCovariance_symmetric A T).eq (L x) (L y)⟩
    (p.auxiliaryCutForm_alternating A S) (fun x => q.auxiliaryCutForm_alternating A T (L x))
    hVpull.symm hΩpull.symm
  exact hc.trans h

/-- A genuine auxiliary-coordinate pullback preserves the selected cut cost;
its image subspace is explicit and is not a restricted optimization ansatz. -/
theorem auxiliaryCutCost_pullbackAuxiliary
    (p : PureCompatibleCovariance (productForm Ω σ))
    (Q : G ≃ₗ[ℝ] F) (hQ : ∀ x y, σ (Q x) (Q y) = τ x y)
    (A : Submodule ℝ E) (T : Submodule ℝ G)
    (hA : (Ω.restrict A).Nondegenerate) (hT : (τ.restrict T).Nondegenerate) :
    (p.pullbackAuxiliary Q hQ).auxiliaryCutCost A T =
      p.auxiliaryCutCost A (T.map Q.toLinearMap) := by
  apply auxiliaryCutCost_transport _ p Q hQ _ A T hA hT
  intro a b x y
  simp

end PureCompatibleCovariance
end Gaussian.Phase
