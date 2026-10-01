import Gaussian.Phase.BosonicPurificationProduct

/-! Explicit standard bosonic coefficient pairs and their unit pure covariance.
These are raw finite real coefficient spaces, without a state realization claim. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The standard real commutator form, with Ω((q,p),(q',p'))=q·p'−p·q'. -/
def standardSymplecticForm : LinearMap.BilinForm ℝ (X × X) :=
  (innerₗ X).compl₁₂ (LinearMap.fst ℝ X X) (LinearMap.snd ℝ X X) -
    (innerₗ X).compl₁₂ (LinearMap.snd ℝ X X) (LinearMap.fst ℝ X X)

@[simp] theorem standardSymplecticForm_apply (x y : X × X) :
    standardSymplecticForm X x y = ⟪x.1,y.2⟫ - ⟪x.2,y.1⟫ := rfl

/-- The standard positive complex structure rotates (q,p) to (−p,q). -/
def standardComplexMap : (X × X) →ₗ[ℝ] (X × X) :=
  (-LinearMap.snd ℝ X X).prod (LinearMap.fst ℝ X X)

@[simp] theorem standardComplexMap_apply (x : X × X) :
    standardComplexMap X x = (-x.2,x.1) := rfl

/-- Explicit unit covariance on every finite number of standard auxiliary modes. -/
def standardPureCovariance : PureCompatibleCovariance (standardSymplecticForm X) where
  form := productForm (innerₗ X) (innerₗ X)
  generator := standardComplexMap X
  symmetric := productForm_symmetric ⟨fun x y => (real_inner_comm x y).symm⟩
    ⟨fun x y => (real_inner_comm x y).symm⟩
  positive x hx := by
    change 0 < ⟪x.1,x.1⟫ + ⟪x.2,x.2⟫
    by_cases h1 : x.1=0
    · have h2 : x.2≠0 := by
        intro h2
        exact hx (Prod.ext h1 h2)
      exact add_pos_of_nonneg_of_pos real_inner_self_nonneg (real_inner_self_pos.mpr h2)
    · exact add_pos_of_pos_of_nonneg (real_inner_self_pos.mpr h1) real_inner_self_nonneg
  square_neg x := by ext <;> simp
  compatible x y := by
    simp only [productForm_apply,standardSymplecticForm_apply,standardComplexMap_apply,
      inner_neg_right,sub_neg_eq_add]
    rfl
  symplectic x y := by
    simp only [standardSymplecticForm_apply,standardComplexMap_apply,inner_neg_left,inner_neg_right]
    ring

@[simp] theorem standardPureCovariance_form (x y : X × X) :
    (standardPureCovariance X).form x y = ⟪x.1,y.1⟫ + ⟪x.2,y.2⟫ := rfl

/-- Standard n-mode auxiliary coefficient space, including n=0. -/
abbrev StandardBosonicSpace (n : ℕ) := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)

theorem finrank_standardBosonicSpace (n : ℕ) :
    finrank ℝ (StandardBosonicSpace n) = 2*n := by
  simp [StandardBosonicSpace,Module.finrank_prod,two_mul]

end Gaussian.Phase
