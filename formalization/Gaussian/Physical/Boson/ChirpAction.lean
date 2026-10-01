import Gaussian.Physical.Boson.WeylImplementation

/-! A concrete quadratic-phase Schrödinger unitary implements every real
symmetric shear. The phase is unbounded; the unitary modulus is exactly one,
so no squeezing or coefficient bound is imposed. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def chirpPhase (S : E →L[ℝ] E) (x : E) : ℝ := ⟪S x,x⟫/2

theorem measurable_chirpPhase (S : E →L[ℝ] E) : Measurable (chirpPhase S) := by
  unfold chirpPhase
  fun_prop

def chirpUnitary (S : E →L[ℝ] E) : Schrodinger E ≃ₗᵢ[ℂ] Schrodinger E :=
  phaseUnitary (chirpPhase S) (measurable_chirpPhase S)

def chirpOperator (S : E →L[ℝ] E) : unitary (Schrodinger E →L[ℂ] Schrodinger E) :=
  Unitary.linearIsometryEquiv.symm (chirpUnitary S)

def chirpShear (S : E →L[ℝ] E) : (E×E) ≃ₗ[ℝ] (E×E) where
  toFun z := (z.1,z.2+S z.1)
  invFun z := (z.1,z.2-S z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp <;> abel
  map_smul' c z := by ext <;> simp [smul_add]

@[simp] theorem chirpShear_apply (S : E →L[ℝ] E) (z : E×E) :
    chirpShear S z = (z.1,z.2+S z.1) := rfl

theorem chirp_phase_identity (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) (q p x : E) :
    phase (weylPhase q p) x * phase (chirpPhase S) (x+q) =
      phase (chirpPhase S) x * phase (weylPhase q (p+S q)) x := by
  unfold phase weylPhase chirpPhase
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  have hs : ⟪S x,q⟫=⟪S q,x⟫ := (hS x q).trans (real_inner_comm x (S q)).symm
  simp only [map_add,inner_add_left,inner_add_right,hs,Complex.ofReal_add,
    Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

theorem chirp_intertwine (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) (q p : E) (f : Schrodinger E) :
    weyl q p (chirpUnitary S f) = chirpUnitary S (weyl q (p+S q) f) := by
  apply Lp.ext
  have hshift := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (phaseMultiply_ae (chirpPhase S) (measurable_chirpPhase S) f)
  filter_upwards [weyl_ae q p (chirpUnitary S f),hshift,
    phaseMultiply_ae (chirpPhase S) (measurable_chirpPhase S) (weyl q (p+S q) f),
    weyl_ae q (p+S q) f] with x h1 h2 h3 h4
  change chirpUnitary S f (x+q) = phase (chirpPhase S) (x+q) * f (x+q) at h2
  change chirpUnitary S (weyl q (p+S q) f) x = _ at h3
  rw [h1,h2,h3,h4]
  rw [← mul_assoc,chirp_phase_identity S hS, mul_assoc]

theorem chirp_implements (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) :
    WeylImplements (chirpShear S) (chirpOperator S) := by
  intro z
  have hi : (weylOperator z.1 z.2 : Schrodinger E →L[ℂ] Schrodinger E) *
      chirpOperator S = (chirpOperator S : Schrodinger E →L[ℂ] Schrodinger E)*
        weylOperator z.1 (z.2+S z.1) := by
    apply ContinuousLinearMap.ext
    intro f
    exact chirp_intertwine S hS z.1 z.2 f
  rw [mul_assoc,hi,← mul_assoc,Unitary.star_mul_self_of_mem (chirpOperator S).property,one_mul]
  rfl

theorem chirpShear_symplectic (S : E →L[ℝ] E)
    (hS : ∀ x y, ⟪S x,y⟫=⟪x,S y⟫) (z w : E×E) :
    weylSymplecticForm E (chirpShear S z) (chirpShear S w)=weylSymplecticForm E z w := by
  simp only [weylSymplecticForm_apply,chirpShear_apply,inner_add_left,inner_add_right,hS]
  ring

end Gaussian.Physical.Boson
