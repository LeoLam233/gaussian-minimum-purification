import Gaussian.Physical.Boson.RankOneContinuity
import Gaussian.Physical.Boson.VacuumCharacteristic

/-! Strong continuity of actual Weyl vector orbits from their characteristic coefficients,
and trace-class integrability of the concrete displaced oscillator vacuum. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open ProbabilisticTheory MeasureTheory
open scoped InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem inner_weyl_vectors (ψ : Schrodinger E) (hψ : ‖ψ‖ = 1) (a b q p : E) :
    ⟪weyl a b ψ, weyl q p ψ⟫_ℂ = weylCocycle (-a) (-b) q p *
      (vectorDensity ψ hψ).characteristic (-a+q) (-b+p) := by
  change ⟪(weylOperator a b : Schrodinger E →L[ℂ] Schrodinger E) ψ,
    (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) ψ⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, weylOperator_star]
  change ⟪ψ, ((weylOperator (-a) (-b) : Schrodinger E →L[ℂ] Schrodinger E) *
    weylOperator q p) ψ⟫_ℂ = _
  rw [weylOperator_mul]
  simp only [smul_apply, inner_smul_right,
    NormalDensity.characteristic, vectorDensity_expect]

/-- This hypothesis is only continuity of a concrete vector's coefficient, not Gaussian realizability. -/
theorem continuous_weyl_vector_of_characteristic (ψ : Schrodinger E) (hψ : ‖ψ‖ = 1)
    (hc : Continuous (fun z : E × E => (vectorDensity ψ hψ).characteristic z.1 z.2)) :
    Continuous (fun z : E × E => weyl z.1 z.2 ψ) := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hmap : Continuous (fun w : E × E => (-z.1+w.1, -z.2+w.2)) :=
    (continuous_fst.const_add (-z.1)).prodMk (continuous_snd.const_add (-z.2))
  have hphase : Continuous (fun w : E × E => weylCocycle (-z.1) (-z.2) w.1 w.2) := by
    unfold weylCocycle
    fun_prop
  have hcomp := hc.comp hmap
  have hi : Continuous (fun w : E × E => ⟪weyl z.1 z.2 ψ, weyl w.1 w.2 ψ⟫_ℂ) := by
    have hcont := hphase.mul hcomp
    apply hcont.congr
    intro w
    exact (inner_weyl_vectors ψ hψ z.1 z.2 w.1 w.2).symm
  have hn : Filter.Tendsto (fun w : E × E => ‖weyl w.1 w.2 ψ - weyl z.1 z.2 ψ‖ ^ 2)
      (𝓝 z) (𝓝 0) := by
    have he : (fun w : E × E => ‖weyl w.1 w.2 ψ - weyl z.1 z.2 ψ‖ ^ 2) =
        fun w => 2 - 2 * (⟪weyl z.1 z.2 ψ, weyl w.1 w.2 ψ⟫_ℂ).re := by
      funext w
      rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ)]
      simp only [LinearIsometryEquiv.norm_map, hψ, one_pow]
      change 1 - 2 * (⟪weyl z.1 z.2 ψ, weyl w.1 w.2 ψ⟫_ℂ).re + 1 = _
      ring
    rw [he]
    have hh : Continuous (fun w : E × E => 2 - 2 * (⟪weyl z.1 z.2 ψ, weyl w.1 w.2 ψ⟫_ℂ).re) :=
      continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hi))
    simpa [inner_self_eq_norm_sq_to_K, hψ] using hh.tendsto z
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn.sqrt

def coherentVector (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (z : ℝ × ℝ) :
    Schrodinger ℝ := weyl z.1 z.2 (oscillatorBasis Q 0)

@[simp] theorem coherentVector_norm (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (z : ℝ × ℝ) :
    ‖coherentVector Q z‖ = 1 := by
  unfold coherentVector
  rw [LinearIsometryEquiv.norm_map, (oscillatorBasis Q).orthonormal.norm_eq_one]

theorem continuous_coherentVector (Q : QuantumMechanics.OneDimension.HarmonicOscillator) :
    Continuous (coherentVector Q) := by
  apply continuous_weyl_vector_of_characteristic _ ((oscillatorBasis Q).orthonormal.norm_eq_one 0)
  simp_rw [oscillator_vacuum_characteristic]
  fun_prop

def coherentDensity (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (z : ℝ × ℝ) :
    NormalDensity (Schrodinger ℝ) := vectorDensity (coherentVector Q z) (coherentVector_norm Q z)

theorem continuous_coherentDensity_operator (Q : QuantumMechanics.OneDimension.HarmonicOscillator) :
    Continuous (fun z : ℝ × ℝ => (coherentDensity Q z).operator) :=
  continuous_vectorOperator.comp (continuous_coherentVector Q)

/-- The concrete coherent ensemble is Bochner-integrable in trace norm for every finite measure. -/
theorem integrable_coherentDensity (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun z => (coherentDensity Q z).operator) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (continuous_coherentDensity_operator Q).aestronglyMeasurable
  filter_upwards with z
  rw [NormalDensity.operator_traceNorm]

end Gaussian.Physical.Boson
