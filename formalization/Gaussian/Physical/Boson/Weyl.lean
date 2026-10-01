import Gaussian.Physical.Boson.PhaseMultiplication
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual finite-dimensional Schrödinger Weyl representation, including zero configuration dimension. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev Schrodinger (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] := Lp (α := E) ℂ 2

def translationIsometry (q : E) : Schrodinger E →ₗᵢ[ℂ] Schrodinger E :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x+q) (measurePreserving_add_right volume q)

theorem translationIsometry_ae (q : E) (f : Schrodinger E) :
    translationIsometry q f =ᵐ[volume] fun x => f (x+q) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume q)

theorem translation_neg_left (q : E) (f : Schrodinger E) :
    translationIsometry (-q) (translationIsometry q f) = f := by
  apply Lp.ext
  have h := (measurePreserving_add_right volume (-q)).quasiMeasurePreserving.ae_eq_comp
    (translationIsometry_ae q f)
  filter_upwards [translationIsometry_ae (-q) (translationIsometry q f), h] with x h1 h2
  simpa only [Function.comp_apply, neg_add_cancel_right] using h1.trans h2

def translationUnitary (q : E) : Schrodinger E ≃ₗᵢ[ℂ] Schrodinger E where
  __ := translationIsometry q
  invFun := translationIsometry (-q)
  left_inv := translation_neg_left q
  right_inv f := by simpa using translation_neg_left (-q) f

def weylPhase (q p : E) (x : E) : ℝ := ⟪p,x⟫_ℝ + ⟪p,q⟫_ℝ / 2

omit [FiniteDimensional ℝ E] in
theorem measurable_weylPhase (q p : E) : Measurable (weylPhase q p) := by
  unfold weylPhase
  fun_prop

def weyl (q p : E) : Schrodinger E ≃ₗᵢ[ℂ] Schrodinger E :=
  (translationUnitary q).trans (phaseUnitary (weylPhase q p) (measurable_weylPhase q p))

theorem weyl_ae (q p : E) (f : Schrodinger E) :
    weyl q p f =ᵐ[volume] fun x => phase (weylPhase q p) x * f (x+q) := by
  have h := phaseMultiply_ae (weylPhase q p) (measurable_weylPhase q p) (translationUnitary q f)
  filter_upwards [h, translationIsometry_ae q f] with x h1 h2
  change phaseMultiply (weylPhase q p) (measurable_weylPhase q p) (translationUnitary q f) x = _
  rw [h1]
  change phase (weylPhase q p) x * translationIsometry q f x = _
  rw [h2]

def weylOperator (q p : E) : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  Unitary.linearIsometryEquiv.symm (weyl q p)

def NormalDensity.displace (ρ : NormalDensity (Schrodinger E)) (q p : E) :
    NormalDensity (Schrodinger E) := ρ.conjugate (weylOperator q p)

theorem NormalDensity.IsPure.displace {ρ : NormalDensity (Schrodinger E)} (hρ : ρ.IsPure)
    (q p : E) : (ρ.displace q p).IsPure := hρ.conjugate _

def weylCocycle (q p q' p' : E) : ℂ :=
  Complex.exp (((⟪p',q⟫_ℝ - ⟪p,q'⟫_ℝ)/2 : ℝ) * Complex.I)

omit [FiniteDimensional ℝ E] in
lemma weyl_phase_product (q p q' p' x : E) :
    phase (weylPhase q p) x * phase (weylPhase q' p') (x+q) =
      weylCocycle q p q' p' * phase (weylPhase (q+q') (p+p')) x := by
  unfold phase weylPhase weylCocycle
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [inner_add_left, inner_add_right, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem weyl_comp_apply (q p q' p' : E) (f : Schrodinger E) :
    weyl q p (weyl q' p' f) = weylCocycle q p q' p' • weyl (q+q') (p+p') f := by
  apply Lp.ext
  have hshift := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (weyl_ae q' p' f)
  filter_upwards [weyl_ae q p (weyl q' p' f), hshift,
    weyl_ae (q+q') (p+p') f,
    Lp.coeFn_smul (weylCocycle q p q' p') (weyl (q+q') (p+p') f)] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2
  rw [h1, h2, h4]
  simp only [Pi.smul_apply, smul_eq_mul, h3, ← mul_assoc, weyl_phase_product, add_assoc]

theorem weyl_zero_apply (f : Schrodinger E) : weyl (0:E) 0 f = f := by
  apply Lp.ext
  filter_upwards [weyl_ae (0:E) 0 f] with x hx
  simpa [phase, weylPhase] using hx

theorem weyl_neg_left (q p : E) (f : Schrodinger E) : weyl (-q) (-p) (weyl q p f) = f := by
  rw [weyl_comp_apply]
  simp [weylCocycle, weyl_zero_apply]

end Gaussian.Physical.Boson
