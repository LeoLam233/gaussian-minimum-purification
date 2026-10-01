import Gaussian.Phase.BosonicPurificationRawFrames
import Gaussian.Phase.BosonicPurificationStandard
import Gaussian.Phase.BosonicPurificationPadding

/-! Every finite raw auxiliary symplectic space and nondegenerate split has
actual canonical sidewise coordinates with proved mode counts. These maps
preserve the original forms and the physical covariance restriction. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

/-- Canonical finite sidewise coordinates for an arbitrary actual auxiliary
split, with no extra existence or full-rank coupling premise. -/
theorem exists_canonical_auxiliary_split (σ : LinearMap.BilinForm ℝ F)
    (hσa : σ.IsAlt) (hσn : σ.Nondegenerate) (S : Submodule ℝ F)
    (hS : (σ.restrict S).Nondegenerate) :
    ∃ a b : ℕ, finrank ℝ S = 2*a ∧ finrank ℝ (σ.orthogonal S) = 2*b ∧
      finrank ℝ F = 2*(a+b) ∧
      ∃ Q : (StandardBosonicSpace a × StandardBosonicSpace b) ≃ₗ[ℝ] F,
        (∀ x y, σ (Q x) (Q y) =
          productForm (standardSymplecticForm (EuclideanSpace ℝ (Fin a)))
            (standardSymplecticForm (EuclideanSpace ℝ (Fin b))) x y) ∧
        (Q.toLinearMap.comp (LinearMap.inl ℝ _ _)).range = S ∧
        (Q.toLinearMap.comp (LinearMap.inr ℝ _ _)).range = σ.orthogonal S := by
  obtain ⟨hCompl,hB⟩ := symplectic_complement_data σ hσa hσn S hS
  obtain ⟨a,ha⟩ := even_finrank_of_nondegenerate_alternating (σ.restrict S)
    (fun x => hσa x) hS
  obtain ⟨b,hb⟩ := even_finrank_of_nondegenerate_alternating (σ.restrict (σ.orthogonal S))
    (fun x => hσa x) hB
  have ha' : finrank ℝ S = 2*a := by omega
  have hb' : finrank ℝ (σ.orthogonal S) = 2*b := by omega
  let pa := standardPureCovariance (EuclideanSpace ℝ (Fin a))
  let pb := standardPureCovariance (EuclideanSpace ℝ (Fin b))
  obtain ⟨A,hA⟩ := exists_raw_symplectic_equiv
    (standardSymplecticForm (EuclideanSpace ℝ (Fin a))) (σ.restrict S)
    pa.commutator_alternating (fun x => hσa x) pa.commutator_nondegenerate hS
    ((finrank_standardBosonicSpace a).trans ha'.symm)
  obtain ⟨B,hBΩ⟩ := exists_raw_symplectic_equiv
    (standardSymplecticForm (EuclideanSpace ℝ (Fin b))) (σ.restrict (σ.orthogonal S))
    pb.commutator_alternating (fun x => hσa x) pb.commutator_nondegenerate hB
    ((finrank_standardBosonicSpace b).trans hb'.symm)
  let Q := (A.prodCongr B).trans (Submodule.prodEquivOfIsCompl S (σ.orthogonal S) hCompl)
  have hQ (x : StandardBosonicSpace a × StandardBosonicSpace b) :
      Q x = (A x.1 : F) + (B x.2 : F) := rfl
  refine ⟨a,b,ha',hb',?_,Q,?_,?_,?_⟩
  · have h := Submodule.finrank_add_eq_of_isCompl hCompl
    omega
  · intro x y
    rw [hQ,hQ]
    change σ ((A x.1 : F)+(B x.2 : F)) ((A y.1 : F)+(B y.2 : F)) = _
    have h₁ : σ (A x.1) (B y.2) = 0 := (B y.2).property (A x.1) (A x.1).property
    have h₂ : σ (B x.2) (A y.1) = 0 :=
      hσa.isRefl _ _ ((B x.2).property (A y.1) (A y.1).property)
    simp only [map_add,LinearMap.add_apply,h₁,h₂,zero_add,add_zero]
    exact congrArg₂ (·+·) (hA x.1 y.1) (hBΩ x.2 y.2)
  · ext x
    constructor
    · rintro ⟨u,rfl⟩
      change Q (u,0) ∈ S
      simp only [hQ,map_zero,Submodule.coe_zero,add_zero]
      exact (A u).property
    · intro hx
      refine ⟨A.symm ⟨x,hx⟩,?_⟩
      change Q (A.symm ⟨x,hx⟩,0) = x
      simp only [hQ,A.apply_symm_apply,map_zero,Submodule.coe_zero,add_zero]
  · ext x
    constructor
    · rintro ⟨u,rfl⟩
      change Q (0,u) ∈ σ.orthogonal S
      simp only [hQ,map_zero,Submodule.coe_zero,zero_add]
      exact (B u).property
    · intro hx
      refine ⟨B.symm ⟨x,hx⟩,?_⟩
      change Q (0,B.symm ⟨x,hx⟩) = x
      simp only [hQ,B.apply_symm_apply,map_zero,Submodule.coe_zero,zero_add]

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}

/-- Transport only the auxiliary coefficient space through an actual symplectic
linear equivalence, preserving the literal physical coordinate. -/
def pullbackAuxiliary (p : PureCompatibleCovariance (productForm Ω σ))
    (Q : G ≃ₗ[ℝ] F) (hQ : ∀ x y, σ (Q x) (Q y) = τ x y) :
    PureCompatibleCovariance (productForm Ω τ) :=
  (p.pullback ((LinearEquiv.refl ℝ E).prodCongr Q)).of_form_eq (by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.1 y.1 + σ (Q x.2) (Q y.2) = Ω x.1 y.1 + τ x.2 y.2
    rw [hQ])

@[simp] theorem pullbackAuxiliary_form (p : PureCompatibleCovariance (productForm Ω σ))
    (Q : G ≃ₗ[ℝ] F) (hQ : ∀ x y, σ (Q x) (Q y) = τ x y) (x y : E × G) :
    (p.pullbackAuxiliary Q hQ).form x y = p.form (x.1,Q x.2) (y.1,Q y.2) := by
  rw [pullbackAuxiliary,of_form_eq_form,pullback_form]
  rfl

@[simp] theorem pullbackAuxiliary_physical (p : PureCompatibleCovariance (productForm Ω σ))
    (Q : G ≃ₗ[ℝ] F) (hQ : ∀ x y, σ (Q x) (Q y) = τ x y) (x y : E) :
    (p.pullbackAuxiliary Q hQ).form (x,0) (y,0) = p.form (x,0) (y,0) := by simp

end PureCompatibleCovariance
end Gaussian.Phase
