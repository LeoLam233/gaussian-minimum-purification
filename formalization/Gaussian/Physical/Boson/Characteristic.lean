import Gaussian.Physical.Boson.Weyl
import Gaussian.Physical.Boson.Observation

/-! Actual Weyl characteristic functions and displacement of their linear term. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[simp] theorem weylOperator_apply (q p : E) (f : Schrodinger E) :
    (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) f = weyl q p f := rfl

theorem weylOperator_mul (q p q' p' : E) :
    (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) * weylOperator q' p' =
      weylCocycle q p q' p' • (weylOperator (q+q') (p+p') : Schrodinger E →L[ℂ] Schrodinger E) := by
  apply ContinuousLinearMap.ext
  intro f
  exact weyl_comp_apply q p q' p' f

@[simp] theorem weylOperator_zero :
    (weylOperator (0:E) 0 : Schrodinger E →L[ℂ] Schrodinger E) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact weyl_zero_apply f

theorem weylOperator_star (q p : E) :
    star (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) = weylOperator (-q) (-p) := by
  have h : (weylOperator (-q) (-p) : Schrodinger E →L[ℂ] Schrodinger E) * weylOperator q p = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    exact weyl_neg_left q p f
  calc
    _ = (weylOperator (-q) (-p) : Schrodinger E →L[ℂ] Schrodinger E) *
      weylOperator q p * star (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) := by rw [h, one_mul]
    _ = _ := by rw [mul_assoc, Unitary.mul_star_self_of_mem (weylOperator q p).property, mul_one]

def NormalDensity.characteristic (ρ : NormalDensity (Schrodinger E)) (q p : E) : ℂ :=
  ρ.expect (weylOperator q p)

@[simp] theorem NormalDensity.characteristic_zero (ρ : NormalDensity (Schrodinger E)) :
    ρ.characteristic 0 0 = 1 := by simp [NormalDensity.characteristic]

theorem NormalDensity.entropy_displace (ρ : NormalDensity (Schrodinger E)) (q p : E) :
    (ρ.displace q p).entropy = ρ.entropy := ρ.entropy_conjugate _

theorem weylOperator_conjugation (a b q p : E) :
    star (weylOperator a b : Schrodinger E →L[ℂ] Schrodinger E) * weylOperator q p *
      weylOperator a b =
      Complex.exp (((⟪b,q⟫_ℝ - ⟪p,a⟫_ℝ) : ℝ) * Complex.I) •
        (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) := by
  rw [weylOperator_star, weylOperator_mul, smul_mul_assoc, weylOperator_mul, smul_smul]
  have hc : weylCocycle (-a) (-b) q p * weylCocycle (-a+q) (-b+p) a b =
      Complex.exp (((⟪b,q⟫_ℝ - ⟪p,a⟫_ℝ) : ℝ) * Complex.I) := by
    unfold weylCocycle
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_neg_left, inner_neg_right, inner_add_right, inner_add_left,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    ring
  rw [hc]
  congr 2 <;> abel

theorem NormalDensity.characteristic_displace (ρ : NormalDensity (Schrodinger E))
    (a b q p : E) :
    (ρ.displace a b).characteristic q p =
      Complex.exp (((⟪b,q⟫_ℝ - ⟪p,a⟫_ℝ) : ℝ) * Complex.I) * ρ.characteristic q p := by
  unfold NormalDensity.characteristic NormalDensity.displace
  rw [NormalDensity.expect_conjugate, weylOperator_conjugation, NormalDensity.expect_smul]

end Gaussian.Physical.Boson
