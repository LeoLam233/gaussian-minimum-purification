import Gaussian.Phase.BosonicPurificationRestriction
import Gaussian.Phase.BosonicPurificationCostTransport

/-! Actual products and pure-mode padding of raw bosonic covariances. Product
forms and generators are defined directly on the coefficient product. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Direct sum of two bilinear forms, allowing unequal finite mode counts. -/
def productForm (V : LinearMap.BilinForm ℝ E) (W : LinearMap.BilinForm ℝ F) :
    LinearMap.BilinForm ℝ (E × F) :=
  V.compl₁₂ (LinearMap.fst ℝ E F) (LinearMap.fst ℝ E F) +
    W.compl₁₂ (LinearMap.snd ℝ E F) (LinearMap.snd ℝ E F)

@[simp] theorem productForm_apply (V : LinearMap.BilinForm ℝ E)
    (W : LinearMap.BilinForm ℝ F) (x y : E × F) :
    productForm V W x y = V x.1 y.1 + W x.2 y.2 := rfl

theorem productForm_symmetric {V : LinearMap.BilinForm ℝ E}
    {W : LinearMap.BilinForm ℝ F} (hV : V.IsSymm) (hW : W.IsSymm) :
    (productForm V W).IsSymm := ⟨fun x y => by
  rw [productForm_apply,productForm_apply,hV.eq,hW.eq]⟩

theorem productForm_alternating {Ω : LinearMap.BilinForm ℝ E}
    {σ : LinearMap.BilinForm ℝ F} (hΩ : Ω.IsAlt) (hσ : σ.IsAlt) :
    (productForm Ω σ).IsAlt := by
  intro x
  rw [productForm_apply,hΩ x.1,hσ x.2,add_zero]

theorem productForm_nondegenerate {Ω : LinearMap.BilinForm ℝ E}
    {σ : LinearMap.BilinForm ℝ F} (hΩ : Ω.Nondegenerate) (hσ : σ.Nondegenerate) :
    (productForm Ω σ).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hΩ.1
      intro y
      simpa using hx (y,0)
    · apply hσ.1
      intro y
      simpa using hx (0,y)
  · intro x hx
    apply Prod.ext
    · apply hΩ.2
      intro y
      simpa using hx (y,0)
    · apply hσ.2
      intro y
      simpa using hx (0,y)

theorem productForm_uncertainty {V Ω : LinearMap.BilinForm ℝ E}
    {W σ : LinearMap.BilinForm ℝ F}
    (hV : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (hW : Gaussian.Covariance.RealifiedUncertainty W σ) :
    Gaussian.Covariance.RealifiedUncertainty (productForm V W) (productForm Ω σ) := by
  intro x y
  simp only [productForm_apply]
  linarith [hV x.1 y.1,hW x.2 y.2]

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

/-- The actual pure product covariance, including a zero-dimensional factor. -/
def prod (p : PureCompatibleCovariance Ω) (q : PureCompatibleCovariance σ) :
    PureCompatibleCovariance (productForm Ω σ) where
  form := productForm p.form q.form
  generator := p.generator.prodMap q.generator
  symmetric := productForm_symmetric p.symmetric q.symmetric
  positive x hx := by
    change 0 < p.form x.1 x.1 + q.form x.2 x.2
    by_cases h1 : x.1=0
    · have h2 : x.2≠0 := by
        intro h2
        apply hx
        exact Prod.ext h1 h2
      exact add_pos_of_nonneg_of_pos (p.nonnegative _) (q.positive _ h2)
    · exact add_pos_of_pos_of_nonneg (p.positive _ h1) (q.nonnegative _)
  square_neg x := by
    apply Prod.ext
    · exact p.square_neg x.1
    · exact q.square_neg x.2
  compatible x y := by
    change p.form x.1 y.1 + q.form x.2 y.2 =
      Ω x.1 (p.generator y.1) + σ x.2 (q.generator y.2)
    rw [p.compatible,q.compatible]
  symplectic x y := by
    change Ω (p.generator x.1) (p.generator y.1) +
        σ (q.generator x.2) (q.generator y.2) = Ω x.1 y.1 + σ x.2 y.2
    rw [p.symplectic,q.symplectic]

@[simp] theorem prod_form (p : PureCompatibleCovariance Ω) (q : PureCompatibleCovariance σ)
    (x y : E × F) : (p.prod q).form x y = p.form x.1 y.1 + q.form x.2 y.2 := rfl

@[simp] theorem prod_physical (p : PureCompatibleCovariance Ω) (q : PureCompatibleCovariance σ)
    (x y : E) : (p.prod q).form (x,0) (y,0) = p.form x y := by simp

/-- The actual adaptation of a pure covariance has amplitude equal to identity. -/
def adaptation (p : PureCompatibleCovariance Ω) : BosonicAdaptationData p.form Ω where
  J := p.generator
  K := LinearMap.id
  g := p.form
  square_neg := p.square_neg
  metric_eq := p.compatible
  metric_symm := p.symmetric
  metric_pos := p.positive
  covariance_factor x y := rfl
  covariance_isometry := p.metric_isometry
  symplectic_isometry := p.symplectic
  commute x := rfl
  amplitude_symm x y := rfl

end PureCompatibleCovariance
namespace BosonicAdaptationData
variable {V Ω : LinearMap.BilinForm ℝ E}

/-- The constructed compatible metric itself is an actual pure covariance. -/
def compatiblePure (d : BosonicAdaptationData V Ω) : PureCompatibleCovariance Ω where
  form := d.g
  generator := d.J
  symmetric := d.metric_symm
  positive := d.metric_pos
  square_neg := d.square_neg
  compatible := d.metric_eq
  symplectic := d.symplectic_isometry

end BosonicAdaptationData
end Gaussian.Phase
