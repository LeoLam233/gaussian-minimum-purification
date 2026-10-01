import Gaussian.Phase.BosonicPurificationSelection
import Gaussian.Phase.BosonicPurificationProductSubspaces
import Gaussian.Phase.BosonicPurificationCostCongruence

/-! One complete auxiliary mode is selected from an excess product cut. The
retained cut is the literal physical factor times a true auxiliary symplectic
complement; equality supplies genuine purity on the removed auxiliary plane. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

def retainedProductMap (S : Submodule ℝ F) : (E × S) →ₗ[ℝ] (E × F) :=
  (LinearMap.id : E →ₗ[ℝ] E).prodMap S.subtype

def productRestriction (V : LinearMap.BilinForm ℝ (E × F)) (S : Submodule ℝ F) :
    LinearMap.BilinForm ℝ (E × S) := V.compl₁₂ (retainedProductMap S) (retainedProductMap S)

def productRestrictionCost (V : LinearMap.BilinForm ℝ (E × F))
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩ : Ω.IsAlt) (hσ : σ.IsAlt) (S : Submodule ℝ F) : ℝ :=
  bosonFormCost (Module.finBasis ℝ (E × S)) (productRestriction V S)
    (productForm Ω (σ.restrict S))
    ⟨fun x y => hV.eq (retainedProductMap S x) (retainedProductMap S y)⟩
    (productForm_alternating hΩ (fun x => hσ x))

/-- A raw excess cut admits a complete auxiliary plane selection, with actual
cost comparison and equality purity. Pure endpoints and zero physical parties
require no extra hypothesis. -/
theorem exists_bosonic_product_selection (V : LinearMap.BilinForm ℝ (E × F))
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V (productForm Ω σ))
    (hExcess : finrank ℝ E < finrank ℝ F) :
    ∃ P : Submodule ℝ F, finrank ℝ P=2 ∧ (σ.restrict P).Nondegenerate ∧
      (σ.restrict (σ.orthogonal P)).Nondegenerate ∧ IsCompl P (σ.orthogonal P) ∧
      finrank ℝ (σ.orthogonal P) = finrank ℝ F-2 ∧
      productRestrictionCost V Ω σ hV hΩa hσa (σ.orthogonal P) ≤
        bosonFormCost (Module.finBasis ℝ (E × F)) V (productForm Ω σ) hV
          (productForm_alternating hΩa hσa) ∧
      (productRestrictionCost V Ω σ hV hΩa hσa (σ.orthogonal P) =
          bosonFormCost (Module.finBasis ℝ (E × F)) V (productForm Ω σ) hV
            (productForm_alternating hΩa hσa) →
        ∃ p : PureCompatibleCovariance (σ.restrict P),
          ∀ x y : P, p.form x y = V (0,x) (0,y)) := by
  let τ := productForm Ω σ
  have hτa := productForm_alternating hΩa hσa
  have hτn := productForm_nondegenerate hΩn hσn
  let A := (LinearMap.inl ℝ E F).range
  have he : finrank ℝ (E × F) < 2*finrank ℝ (τ.orthogonal A) := by
    rw [productForm_orthogonal_physical Ω σ hΩn,
      LinearMap.finrank_range_of_inj (LinearMap.inr_injective (R := ℝ) (M := E) (M₂ := F)),Module.finrank_prod]
    omega
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating τ hτa hτn
  have hn' : finrank ℝ (E × F)=2*n := by omega
  let e := modeBasisOfFinrankEq hn'
  obtain ⟨P,hPd,hPA,hAP,hPn,hUn,hCompl,hUd,eU,hcost,hpure⟩ :=
    exists_bosonic_covariance_selection V τ hV hτa hτn hUnc A he e
  have hPaux : P ≤ (LinearMap.inr ℝ E F).range := by
    change P ≤ (productForm Ω σ).orthogonal (LinearMap.inl ℝ E F).range at hPA
    rw [productForm_orthogonal_physical Ω σ hΩn] at hPA
    exact hPA
  let Q := P.comap (LinearMap.inr ℝ E F)
  let LQ := auxiliaryOnlyEquiv P hPaux
  have hQd : finrank ℝ Q=2 := LQ.finrank_eq.trans hPd
  have hQform : (τ.restrict P).compl₁₂ LQ.toLinearMap LQ.toLinearMap = σ.restrict Q := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω 0 0 + σ x y = σ x y
    simp
  have hQn : (σ.restrict Q).Nondegenerate := by
    rw [← hQform]
    exact (form_nondegenerate_pullback_iff _ LQ).mpr hPn
  obtain ⟨hQC,hWn⟩ := symplectic_complement_data σ hσa hσn Q hQn
  have hU : τ.orthogonal P = (⊤ : Submodule ℝ E).prod (σ.orthogonal Q) := by
    rw [← auxiliaryOnly_map_eq P hPaux]
    exact productForm_orthogonal_auxiliary Ω σ Q
  let L := (fullProductSubspaceEquiv (E := E) (σ.orthogonal Q)).trans
    (LinearEquiv.ofEq _ _ hU.symm)
  have hL (x : E × σ.orthogonal Q) : (L x : E × F) = (x.1,(x.2 : F)) := rfl
  have hCost := bosonFormCost_pullback_general (V.restrict (τ.orthogonal P))
    (τ.restrict (τ.orthogonal P)) (hV.restrict _) (fun x => hτa x) hUn
    (fun x y => hUnc x y) L eU (Module.finBasis ℝ (E × σ.orthogonal Q))
  have hCost' : productRestrictionCost V Ω σ hV hΩa hσa (σ.orthogonal Q) =
      bosonFormCost eU (V.restrict (τ.orthogonal P)) (τ.restrict (τ.orthogonal P))
        (hV.restrict _) (fun x => hτa x) := hCost
  have hOrig := bosonFormCost_basis_independent_general V τ hV hτa hτn hUnc e
    (Module.finBasis ℝ (E × F))
  refine ⟨Q,hQd,hQn,hWn,hQC,?_,?_,?_⟩
  · rw [LinearMap.BilinForm.finrank_orthogonal hσn,hQd]
  · exact hCost'.trans_le (hcost.trans_eq hOrig)
  · intro heq
    obtain ⟨p,hp⟩ := hpure (hCost'.symm.trans (heq.trans hOrig.symm))
    refine ⟨(p.pullback LQ).of_form_eq hQform,?_⟩
    intro x y
    rw [PureCompatibleCovariance.of_form_eq_form,PureCompatibleCovariance.pullback_form,hp]
    rfl

end Gaussian.Phase
