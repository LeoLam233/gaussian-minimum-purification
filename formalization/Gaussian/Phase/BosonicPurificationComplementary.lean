import Gaussian.Phase.BosonicPurificationReference
import Gaussian.Phase.BosonicPurificationCrossOrbit

/-! Complementary symplectic restrictions of an actual pure covariance have
exactly equal independently defined two-form costs. The proof uses the explicit
balanced reference, pure padding and the proved raw auxiliary orbit. No state
Schmidt decomposition or density entropy equality is assumed. -/
noncomputable section
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

def leftCovariance (p : PureCompatibleCovariance (productForm Ω σ)) :
    LinearMap.BilinForm ℝ E := p.form.compl₁₂ (LinearMap.inl ℝ E F) (LinearMap.inl ℝ E F)

def rightCovariance (p : PureCompatibleCovariance (productForm Ω σ)) :
    LinearMap.BilinForm ℝ F := p.form.compl₁₂ (LinearMap.inr ℝ E F) (LinearMap.inr ℝ E F)

theorem leftCovariance_symmetric (p : PureCompatibleCovariance (productForm Ω σ)) :
    p.leftCovariance.IsSymm := ⟨fun x y => p.symmetric.eq (x,0) (y,0)⟩

theorem rightCovariance_symmetric (p : PureCompatibleCovariance (productForm Ω σ)) :
    p.rightCovariance.IsSymm := ⟨fun x y => p.symmetric.eq (0,x) (0,y)⟩

theorem leftCovariance_uncertainty (p : PureCompatibleCovariance (productForm Ω σ)) :
    Gaussian.Covariance.RealifiedUncertainty p.leftCovariance Ω := by
  intro x y
  simpa [leftCovariance] using p.uncertainty (x,0) (y,0)

theorem rightCovariance_uncertainty (p : PureCompatibleCovariance (productForm Ω σ)) :
    Gaussian.Covariance.RealifiedUncertainty p.rightCovariance σ := by
  intro x y
  simpa [rightCovariance] using p.uncertainty (0,x) (0,y)

/-- Interchange the two actual coefficient factors and their two commutator forms. -/
def swap (p : PureCompatibleCovariance (productForm Ω σ)) :
    PureCompatibleCovariance (productForm σ Ω) :=
  (p.pullback (LinearEquiv.prodComm ℝ F E)).of_form_eq (by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Ω x.2 y.2 + σ x.1 y.1 = σ x.1 y.1 + Ω x.2 y.2
    exact add_comm _ _)

@[simp] theorem swap_form (p : PureCompatibleCovariance (productForm Ω σ)) (x y : F × E) :
    p.swap.form x y = p.form (x.2,x.1) (y.2,y.1) := by simp [swap,Prod.swap]

@[simp] theorem leftCovariance_swap (p : PureCompatibleCovariance (productForm Ω σ)) :
    p.swap.leftCovariance = p.rightCovariance := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact p.swap_form (x,0) (y,0)

@[simp] theorem rightCovariance_swap (p : PureCompatibleCovariance (productForm Ω σ)) :
    p.swap.rightCovariance = p.leftCovariance := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact p.swap_form (0,x) (0,y)

theorem complementary_formCost_of_finrank_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : PureCompatibleCovariance (productForm Ω σ)) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hd : finrank ℝ E ≤ finrank ℝ F) (e : Basis ι ℝ E) (f : Basis κ ℝ F) :
    bosonFormCost e p.leftCovariance Ω p.leftCovariance_symmetric hΩa =
      bosonFormCost f p.rightCovariance σ p.rightCovariance_symmetric hσa := by
  obtain ⟨q,hq,hqcost⟩ := exists_bosonic_reference_with_auxiliary_cost
    p.leftCovariance Ω σ p.leftCovariance_symmetric hΩa hσa hΩn hσn
    p.leftCovariance_uncertainty hd e f
  obtain ⟨Q,hQ,hcov⟩ := exists_pure_covariance_auxiliary_equiv Ω σ σ hΩn p q rfl
    (fun x y => (hq x y).symm)
  have hV : q.rightCovariance.compl₁₂ Q.toLinearMap Q.toLinearMap = p.rightCovariance := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hcov 0 0 x y
  have hσ : σ.compl₁₂ Q.toLinearMap Q.toLinearMap = σ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hQ x y
  have hcost := bosonFormCost_pullback_general q.rightCovariance σ q.rightCovariance_symmetric
    hσa hσn q.rightCovariance_uncertainty Q f f
  have hc := bosonFormCost_congr_forms f
    (V₁ := p.rightCovariance) (V₂ := q.rightCovariance.compl₁₂ Q.toLinearMap Q.toLinearMap)
    (Ω₁ := σ) (Ω₂ := σ.compl₁₂ Q.toLinearMap Q.toLinearMap) p.rightCovariance_symmetric
    ⟨fun x y => q.rightCovariance_symmetric.eq (Q x) (Q y)⟩
    hσa (fun x => hσa (Q x)) hV.symm hσ.symm
  exact hqcost.symm.trans (hc.trans hcost).symm

/-- Exact complementary-cut covariance cost equality in every finite dimension. -/
theorem complementary_formCost
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : PureCompatibleCovariance (productForm Ω σ)) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) :
    bosonFormCost e p.leftCovariance Ω p.leftCovariance_symmetric hΩa =
      bosonFormCost f p.rightCovariance σ p.rightCovariance_symmetric hσa := by
  rcases le_total (finrank ℝ E) (finrank ℝ F) with hd | hd
  · exact p.complementary_formCost_of_finrank_le hΩa hσa hΩn hσn hd e f
  · have h := p.swap.complementary_formCost_of_finrank_le hσa hΩa hσn hΩn hd f e
    simpa only [leftCovariance_swap,rightCovariance_swap] using h.symm

end PureCompatibleCovariance
end Gaussian.Phase
