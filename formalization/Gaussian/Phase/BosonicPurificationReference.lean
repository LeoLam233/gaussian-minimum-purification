import Gaussian.Phase.BosonicPurification
import Gaussian.Phase.BosonicPurificationBalanced
import Gaussian.Phase.BosonicPurificationCostCongruence
import Gaussian.Phase.BosonicPurificationPadding
import Gaussian.Phase.BosonicPurificationStandard
import Gaussian.Phase.BosonicPurificationRawFrames

/-! Raw reference covariances at every sufficiently large auxiliary dimension.
Padding and a proved symplectic equivalence produce the literal prescribed
auxiliary commutator form and exact physical covariance restriction. -/
noncomputable section
open Module
namespace Gaussian.Phase

/-- Every admissible physical pair has an actual pure reference with any fixed
finite auxiliary symplectic space at least as large as the physical space. -/
theorem exists_bosonic_reference_with_auxiliary
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (V Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (hsize : finrank ℝ E ≤ finrank ℝ F) :
    ∃ p : PureCompatibleCovariance (productForm Ω σ),
      ∀ x y, p.form (x,0) (y,0) = V x y := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  obtain ⟨m,hm⟩ := even_finrank_of_nondegenerate_alternating σ hσa hσn
  obtain ⟨p₀,hp₀,_⟩ := exists_bosonic_reference_compatible V Ω hV hΩa hΩn hUnc
  let X := StandardBosonicSpace (m-n)
  let q₀ := standardPureCovariance (EuclideanSpace ℝ (Fin (m-n)))
  let σ₀ := standardSymplecticForm (EuclideanSpace ℝ (Fin (m-n)))
  have hdim : finrank ℝ F = finrank ℝ (E × X) := by
    rw [Module.finrank_prod,finrank_standardBosonicSpace]
    omega
  obtain ⟨q,hq⟩ := exists_raw_symplectic_equiv σ (productForm Ω σ₀)
    hσa (productForm_alternating hΩa q₀.commutator_alternating)
    hσn (productForm_nondegenerate hΩn q₀.commutator_nondegenerate) hdim
  let L : (E × F) ≃ₗ[ℝ] ((E × E) × X) :=
    ((LinearEquiv.refl ℝ E).prodCongr q).trans (LinearEquiv.prodAssoc ℝ E E X).symm
  let p := p₀.prod q₀
  have hform : (productForm (doubledForm Ω Ω) σ₀).compl₁₂ L.toLinearMap L.toLinearMap =
      productForm Ω σ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.1 y.1 + Ω (q x.2).1 (q y.2).1 + σ₀ (q x.2).2 (q y.2).2 =
      Ω x.1 y.1 + σ x.2 y.2
    rw [add_assoc]
    exact congrArg (fun z => Ω x.1 y.1 + z) (hq x.2 y.2)
  refine ⟨(p.pullback L).of_form_eq hform,?_⟩
  intro x y
  rw [PureCompatibleCovariance.of_form_eq_form,PureCompatibleCovariance.pullback_form]
  change p₀.form (x,(q 0).1) (y,(q 0).1) + q₀.form (q 0).2 (q 0).2 = V x y
  simp only [map_zero,Prod.fst_zero,Prod.snd_zero,LinearMap.zero_apply,add_zero]
  exact hp₀ x y

/-- The padded reference can be chosen with exact equality between the auxiliary
and original physical two-form costs, for arbitrary finite coefficient bases. -/
theorem exists_bosonic_reference_with_auxiliary_cost
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (hsize : finrank ℝ E ≤ finrank ℝ F) (e : Basis ι ℝ E) (f : Basis κ ℝ F) :
    ∃ p : PureCompatibleCovariance (productForm Ω σ),
      (∀ x y, p.form (x,0) (y,0) = V x y) ∧
      bosonFormCost f (p.form.compl₁₂ (LinearMap.inr ℝ E F) (LinearMap.inr ℝ E F)) σ
        ⟨fun x y => p.symmetric.eq (0,x) (0,y)⟩ hσa = bosonFormCost e V Ω hV hΩa := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  obtain ⟨m,hm⟩ := even_finrank_of_nondegenerate_alternating σ hσa hσn
  obtain ⟨p₀,hp₀,hp₀aux⟩ := exists_balanced_bosonic_reference V Ω hV hΩa hΩn hUnc
  let X := StandardBosonicSpace (m-n)
  let q₀ := standardPureCovariance (EuclideanSpace ℝ (Fin (m-n)))
  let σ₀ := standardSymplecticForm (EuclideanSpace ℝ (Fin (m-n)))
  have hdim : finrank ℝ F = finrank ℝ (E × X) := by
    rw [Module.finrank_prod,finrank_standardBosonicSpace]
    omega
  obtain ⟨q,hq⟩ := exists_raw_symplectic_equiv σ (productForm Ω σ₀)
    hσa (productForm_alternating hΩa q₀.commutator_alternating)
    hσn (productForm_nondegenerate hΩn q₀.commutator_nondegenerate) hdim
  let L : (E × F) ≃ₗ[ℝ] ((E × E) × X) :=
    ((LinearEquiv.refl ℝ E).prodCongr q).trans (LinearEquiv.prodAssoc ℝ E E X).symm
  let p := p₀.prod q₀
  have hform : (productForm (doubledForm Ω Ω) σ₀).compl₁₂ L.toLinearMap L.toLinearMap =
      productForm Ω σ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.1 y.1 + Ω (q x.2).1 (q y.2).1 + σ₀ (q x.2).2 (q y.2).2 =
      Ω x.1 y.1 + σ x.2 y.2
    rw [add_assoc]
    exact congrArg (fun z => Ω x.1 y.1 + z) (hq x.2 y.2)
  let P := (p.pullback L).of_form_eq hform
  have hAux : P.form.compl₁₂ (LinearMap.inr ℝ E F) (LinearMap.inr ℝ E F) =
      (productForm V q₀.form).compl₁₂ q.toLinearMap q.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change P.form (0,x) (0,y) = V (q x).1 (q y).1 + q₀.form (q x).2 (q y).2
    dsimp only [P]
    rw [PureCompatibleCovariance.of_form_eq_form,PureCompatibleCovariance.pullback_form]
    change p₀.form (0,(q x).1) (0,(q y).1) + q₀.form (q x).2 (q y).2 = _
    rw [hp₀aux]
  have hσpull : (productForm Ω σ₀).compl₁₂ q.toLinearMap q.toLinearMap = σ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hq x y
  refine ⟨P,?_,?_⟩
  · intro x y
    dsimp only [P]
    rw [PureCompatibleCovariance.of_form_eq_form,PureCompatibleCovariance.pullback_form]
    change p₀.form (x,(q 0).1) (y,(q 0).1) + q₀.form (q 0).2 (q 0).2 = V x y
    simp only [map_zero,Prod.fst_zero,Prod.snd_zero,LinearMap.zero_apply,add_zero]
    exact hp₀ x y
  · have h := bosonFormCost_pullback_general (productForm V q₀.form) (productForm Ω σ₀)
      (productForm_symmetric hV q₀.symmetric) (productForm_alternating hΩa q₀.commutator_alternating)
      (productForm_nondegenerate hΩn q₀.commutator_nondegenerate)
      (productForm_uncertainty hUnc q₀.uncertainty) q (Module.finBasis ℝ (E × X)) f
    have hc := bosonFormCost_congr_forms f
      (V₁ := P.form.compl₁₂ (LinearMap.inr ℝ E F) (LinearMap.inr ℝ E F))
      (V₂ := (productForm V q₀.form).compl₁₂ q.toLinearMap q.toLinearMap)
      (Ω₁ := σ) (Ω₂ := (productForm Ω σ₀).compl₁₂ q.toLinearMap q.toLinearMap)
      ⟨fun x y => P.symmetric.eq (0,x) (0,y)⟩
      ⟨fun x y => (productForm_symmetric hV q₀.symmetric).eq (q x) (q y)⟩
      hσa (fun x => productForm_alternating hΩa q₀.commutator_alternating (q x))
      hAux hσpull.symm
    exact hc.trans (h.trans (bosonFormCost_pure_padding V Ω σ₀ hV hΩa hΩn hUnc q₀
      e (Module.finBasis ℝ X) (Module.finBasis ℝ (E × X))))

end Gaussian.Phase
