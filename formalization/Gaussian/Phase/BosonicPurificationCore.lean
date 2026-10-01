import Gaussian.Phase.BosonicPurificationBlocks
import Gaussian.Phase.BosonicOrbit
import Gaussian.Covariance.Uncertainty

/-! Raw pure compatible covariance forms and invertible squeezing maps.
These algebraic objects assert no density-state realization or entropy theorem. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section RawForms
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Covariance-only purity: a positive compatible metric whose actual
commutator generator is a square root of minus identity. -/
structure PureCompatibleCovariance (Ω : LinearMap.BilinForm ℝ E) where
  form : LinearMap.BilinForm ℝ E
  generator : E →ₗ[ℝ] E
  symmetric : form.IsSymm
  positive : ∀ x, x ≠ 0 → 0 < form x x
  square_neg : ∀ x, generator (generator x) = -x
  compatible : ∀ x y, form x y = Ω x (generator y)
  symplectic : ∀ x y, Ω (generator x) (generator y) = Ω x y

namespace PureCompatibleCovariance
variable {Ω : LinearMap.BilinForm ℝ E} (d : PureCompatibleCovariance Ω)

theorem nonnegative (x : E) : 0 ≤ d.form x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (d.positive x hx).le

theorem metric_isometry (x y : E) :
    d.form (d.generator x) (d.generator y) = d.form x y := by
  rw [d.compatible,d.compatible]
  exact d.symplectic x (d.generator y)

/-- Raw uncertainty is proved from the positive compatible metric; it is not
an extra semantic assertion inserted into the covariance data. -/
theorem uncertainty : Gaussian.Covariance.RealifiedUncertainty d.form Ω := by
  intro x y
  have hcross : d.form x (d.generator y) = -Ω x y := by
    rw [d.compatible,d.square_neg,map_neg]
  calc
    0 ≤ d.form (x+d.generator y) (x+d.generator y) := d.nonnegative _
    _ = d.form x x + d.form y y - 2*Ω x y := by
      simp only [map_add,LinearMap.add_apply]
      rw [d.metric_isometry,d.symmetric.eq (d.generator y) x,hcross]
      ring

/-- Pull back both original forms and the generator through an actual linear
equivalence, preserving every coefficient-level purity condition. -/
def pullback (e : F ≃ₗ[ℝ] E) : PureCompatibleCovariance
    (Ω.compl₁₂ e.toLinearMap e.toLinearMap) where
  form := d.form.compl₁₂ e.toLinearMap e.toLinearMap
  generator := e.symm.conj d.generator
  symmetric := ⟨fun x y => d.symmetric.eq (e x) (e y)⟩
  positive x hx := d.positive (e x) (by
    intro h
    apply hx
    exact e.injective (h.trans e.map_zero.symm))
  square_neg x := by simp [LinearEquiv.conj_apply,d.square_neg]
  compatible x y := by
    change d.form (e x) (e y) = Ω (e x) (e (e.symm (d.generator (e y))))
    rw [e.apply_symm_apply]
    exact d.compatible _ _
  symplectic x y := by
    change Ω (e (e.symm (d.generator (e x)))) (e (e.symm (d.generator (e y)))) = Ω (e x) (e y)
    rw [e.apply_symm_apply,e.apply_symm_apply,d.symplectic]

@[simp] theorem pullback_form (e : F ≃ₗ[ℝ] E) (x y : F) :
    (d.pullback e).form x y = d.form (e x) (e y) := rfl


/-- Re-express a proved covariance over an equal raw commutator form. -/
def of_form_eq {Ω' : LinearMap.BilinForm ℝ E} (h : Ω = Ω') :
    PureCompatibleCovariance Ω' := h ▸ d

@[simp] theorem of_form_eq_form {Ω' : LinearMap.BilinForm ℝ E} (h : Ω = Ω') (x y : E) :
    (d.of_form_eq h).form x y = d.form x y := by cases h; rfl

end PureCompatibleCovariance

/-- Direct sum of two raw bilinear forms, with its two summands explicit. -/
def doubledForm (B₁ B₂ : LinearMap.BilinForm ℝ E) : LinearMap.BilinForm ℝ (E × E) :=
  B₁.compl₁₂ (LinearMap.fst ℝ E E) (LinearMap.fst ℝ E E) +
    B₂.compl₁₂ (LinearMap.snd ℝ E E) (LinearMap.snd ℝ E E)

@[simp] theorem doubledForm_apply (B₁ B₂ : LinearMap.BilinForm ℝ E) (x y : E × E) :
    doubledForm B₁ B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 := rfl

@[simp] theorem doubledForm_physical (B₁ B₂ : LinearMap.BilinForm ℝ E) (x y : E) :
    doubledForm B₁ B₂ (x,0) (y,0) = B₁ x y := by simp

theorem doubledForm_alternating (B₁ B₂ : LinearMap.BilinForm ℝ E)
    (h₁ : B₁.IsAlt) (h₂ : B₂.IsAlt) : (doubledForm B₁ B₂).IsAlt := by
  intro x
  simp only [doubledForm_apply,h₁ x.1,h₂ x.2,add_zero]

/-- The two-copy squeezing map. No inverse of S or of a mixed defect is used. -/
def squeezingMap (C S : E →ₗ[ℝ] E) : (E × E) →ₗ[ℝ] (E × E) :=
  (C.coprod S).prod (S.coprod C)

@[simp] theorem squeezingMap_apply (C S : E →ₗ[ℝ] E) (x : E × E) :
    squeezingMap C S x = (C x.1 + S x.2,S x.1+C x.2) := rfl

/-- C²-S²=I gives an explicit inverse even when S has a kernel. -/
def squeezingEquiv (C S : E →ₗ[ℝ] E)
    (hcomm : ∀ x, C (S x) = S (C x))
    (hsq : ∀ x, C (C x) - S (S x) = x) : (E × E) ≃ₗ[ℝ] (E × E) where
  toLinearMap := squeezingMap C S
  invFun x := (C x.1-S x.2,C x.2-S x.1)
  left_inv x := by
    apply Prod.ext
    · change C (C x.1+S x.2) - S (S x.1+C x.2) = x.1
      simp only [map_add,hcomm]
      calc
        _ = C (C x.1)-S (S x.1) := by abel
        _ = x.1 := hsq x.1
    · change C (S x.1+C x.2) - S (C x.1+S x.2) = x.2
      simp only [map_add,hcomm]
      calc
        _ = C (C x.2)-S (S x.2) := by abel
        _ = x.2 := hsq x.2
  right_inv x := by
    apply Prod.ext
    · change C (C x.1-S x.2) + S (C x.2-S x.1) = x.1
      simp only [map_sub,hcomm]
      calc
        _ = C (C x.1)-S (S x.1) := by abel
        _ = x.1 := hsq x.1
    · change S (C x.1-S x.2) + C (C x.2-S x.1) = x.2
      simp only [map_sub,hcomm]
      calc
        _ = C (C x.2)-S (S x.2) := by abel
        _ = x.2 := hsq x.2

@[simp] theorem squeezingEquiv_apply (C S : E →ₗ[ℝ] E)
    (hcomm : ∀ x, C (S x) = S (C x)) (hsq : ∀ x, C (C x)-S (S x)=x)
    (x : E × E) : squeezingEquiv C S hcomm hsq x = (C x.1+S x.2,S x.1+C x.2) := rfl

end RawForms

section InnerForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unsqueezed pure covariance on opposite-form copies, with its actual
positive Gram form and actual diagonal complex structure. -/
def basePureDouble (J : OrthogonalComplexStructure E) :
    PureCompatibleCovariance (doubledForm J.symplecticForm (-J.symplecticForm)) where
  form := doubledForm (innerₗ E) (innerₗ E)
  generator := J.linear.prodMap (-J.linear)
  symmetric := ⟨fun x y => by
    change ⟪x.1,y.1⟫ + ⟪x.2,y.2⟫ = ⟪y.1,x.1⟫ + ⟪y.2,x.2⟫
    rw [real_inner_comm x.1 y.1,real_inner_comm x.2 y.2]⟩
  positive x hx := by
    change 0 < ⟪x.1,x.1⟫ + ⟪x.2,x.2⟫
    by_contra hh
    have h₁ : 0 ≤ ⟪x.1,x.1⟫ := real_inner_self_nonneg
    have h₂ : 0 ≤ ⟪x.2,x.2⟫ := real_inner_self_nonneg
    have hz₁ : ⟪x.1,x.1⟫ = 0 := by linarith
    have hz₂ : ⟪x.2,x.2⟫ = 0 := by linarith
    apply hx
    exact Prod.ext (inner_self_eq_zero.mp hz₁) (inner_self_eq_zero.mp hz₂)
  square_neg x := by
    apply Prod.ext
    · exact J.square_neg x.1
    · change -J (-J x.2) = -x.2
      simp
  compatible x y := by
    change ⟪x.1,y.1⟫ + ⟪x.2,y.2⟫ =
      J.symplecticForm x.1 (J y.1) - J.symplecticForm x.2 (-J y.2)
    simp [OrthogonalComplexStructure.symplecticForm_apply]
  symplectic x y := by
    change J.symplecticForm (J x.1) (J y.1) - J.symplecticForm (-J x.2) (-J y.2) =
      J.symplecticForm x.1 y.1 - J.symplecticForm x.2 y.2
    simp [J.symplecticForm_map_map,J.inner_map_left]

end InnerForms
end Gaussian.Phase
