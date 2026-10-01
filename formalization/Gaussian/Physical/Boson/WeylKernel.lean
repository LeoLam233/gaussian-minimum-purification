import Gaussian.Physical.Boson.NuclearExpansion
import Gaussian.Physical.Boson.Weyl
import Gaussian.Physical.Boson.FourierInjectivity
import Mathlib.MeasureTheory.Function.Holder

/-! Actual L1 sections of trace-class nuclear kernels and their Weyl Fourier coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory
open scoped InnerProductSpace FourierTransform
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tracePairing_outerOperator (A : H →L[ℂ] H) (u v : H) :
    TraceClass.tracePairing A (outerOperator u v) = ⟪v,A u⟫_ℂ := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
  rw [TraceClass.tracePairing_apply, trace_eq_of_hilbertBasis _ b]
  simpa only [outerOperator_coe, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right] using
    b.tsum_inner_mul_inner v (A u)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_star_schrodinger (v : Schrodinger E) : ‖star v‖ = ‖v‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [Lp.coeFn_star v] with x hx
    rw [hx]; simp
  · filter_upwards [Lp.coeFn_star v] with x hx
    rw [hx]; simp

def rankOneSection (q : E) (u v : Schrodinger E) : Lp (α := E) ℂ 1 :=
  translationIsometry q u • star v

lemma rankOneSection_ae (q : E) (u v : Schrodinger E) :
    rankOneSection q u v =ᵐ[volume] fun x => u (x+q) * star (v x) := by
  filter_upwards [Lp.coeFn_lpSMul (r := 1) (translationIsometry q u) (star v),
    translationIsometry_ae q u, Lp.coeFn_star v] with x h1 h2 h3
  change (translationIsometry q u • star v : Lp (α := E) ℂ 1) x = _
  simpa only [h1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, h2, h3, Pi.star_apply]

lemma norm_rankOneSection_le (q : E) (u v : Schrodinger E) :
    ‖rankOneSection q u v‖ ≤ ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ‖translationIsometry q u‖ * ‖star v‖ := Lp.norm_smul_le _ _
    _ = _ := by rw [(translationIsometry q).norm_map, norm_star_schrodinger]

/-- Nuclear kernel sections converge absolutely in L1 for each configuration shift. -/
lemma summable_norm_rankOneSection {ι : Type*} (u v : ι → Schrodinger E)
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)) (q : E) :
    Summable (fun i => ‖rankOneSection q (u i) (v i)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_rankOneSection_le ..) huv

def nuclearSection {ι : Type*} (u v : ι → Schrodinger E) (q : E) : Lp (α := E) ℂ 1 :=
  ∑' i, rankOneSection q (u i) (v i)

lemma inner_weyl_eq_fourier_section (q p : E) (u v : Schrodinger E) :
    ⟪v,weyl q p u⟫_ℂ = Complex.exp ((⟪p,q⟫_ℝ / 2 : ℝ) * Complex.I) *
      𝓕 (rankOneSection q u v : E → ℂ) (-((2*Real.pi)⁻¹) • p) := by
  rw [L2.inner_def, Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [weyl_ae q p u, rankOneSection_ae q u v] with x hw hk
  rw [hw, hk]
  have hi : -2 * Real.pi * ⟪x,-((2*Real.pi)⁻¹) • p⟫_ℝ = ⟪p,x⟫_ℝ := by
    rw [inner_smul_right, real_inner_comm x p]
    field_simp
  simp only [hi, inner, smul_eq_mul, phase, weylPhase]
  have he : Complex.exp (((⟪p,x⟫_ℝ + ⟪p,q⟫_ℝ/2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((⟪p,q⟫_ℝ/2 : ℝ) * Complex.I) *
      Complex.exp ((⟪p,x⟫_ℝ : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The Weyl characteristic of an absolutely nuclear sum is the Fourier transform of its L1 section. -/
theorem tracePairing_nuclear_eq_fourier {ι : Type*} (u v : ι → Schrodinger E)
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖)) (q p : E) :
    TraceClass.tracePairing (weylOperator q p) (∑' i, outerOperator (u i) (v i)) =
      Complex.exp ((⟪p,q⟫_ℝ / 2 : ℝ) * Complex.I) *
        𝓕 (nuclearSection u v q : E → ℂ) (-((2*Real.pi)⁻¹) • p) := by
  have ho : Summable (fun i => outerOperator (u i) (v i)) := by
    apply Summable.of_norm
    simpa only [norm_outerOperator] using huv
  let F : Lp (α := E) ℂ 1 →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (-((2*Real.pi)⁻¹) • p)).comp
      (Real.Lp.fourierTransformCLM E ℂ)
  have hs := ((summable_norm_rankOneSection u v huv q).of_norm.hasSum.mapL F).mul_left
    (Complex.exp ((⟪p,q⟫_ℝ / 2 : ℝ) * Complex.I))
  have ht := ho.hasSum.mapL (TraceClass.tracePairing (weylOperator q p))
  have he : ∀ i, TraceClass.tracePairing (weylOperator q p) (outerOperator (u i) (v i)) =
      Complex.exp ((⟪p,q⟫_ℝ / 2 : ℝ) * Complex.I) * F (rankOneSection q (u i) (v i)) := by
    intro i
    rw [tracePairing_outerOperator]
    exact inner_weyl_eq_fourier_section q p (u i) (v i)
  have ht' : HasSum (fun i => Complex.exp ((⟪p,q⟫_ℝ / 2 : ℝ) * Complex.I) *
      F (rankOneSection q (u i) (v i)))
      (TraceClass.tracePairing (weylOperator q p) (∑' i, outerOperator (u i) (v i))) := by
    simpa only [← he] using ht
  exact ht'.unique hs

/-- Vanishing Weyl data forces every actual nuclear kernel section to vanish in L1. -/
theorem nuclearSection_eq_zero_of_weyl_zero {ι : Type*} (u v : ι → Schrodinger E)
    (huv : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hzero : ∀ q p : E, TraceClass.tracePairing (weylOperator q p)
      (∑' i, outerOperator (u i) (v i)) = 0) (q : E) : nuclearSection u v q = 0 := by
  apply Lp.ext
  have hf : 𝓕 (nuclearSection u v q : E → ℂ) = 0 := by
    funext ξ
    have h := hzero q ((-(2*Real.pi)) • ξ)
    rw [tracePairing_nuclear_eq_fourier u v huv] at h
    have hp : -((2*Real.pi)⁻¹) • ((-(2*Real.pi)) • ξ) = ξ := by
      rw [smul_smul]
      have hh : -((2*Real.pi)⁻¹) * -(2*Real.pi) = 1 := by field_simp
      rw [hh, one_smul]
    rw [hp] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  filter_upwards [ae_eq_zero_of_fourier_eq_zero_finite (L1.integrable_coeFn _) hf,
    Lp.coeFn_zero ℂ 1 (volume : Measure E)] with x hx hz
  exact hx.trans hz.symm

end Gaussian.Physical.Boson
