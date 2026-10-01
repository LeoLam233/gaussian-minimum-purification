import Gaussian.Physical.Boson.KernelTesting
import Gaussian.Physical.Boson.CountableNuclear
import Gaussian.Physical.Boson.Characteristic

/-! Injectivity of the genuine Schrödinger Weyl characteristic on the full trace class.
The proof is nuclear L1 Fourier uniqueness followed by Schwartz correlation testing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory SchwartzMap
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma nuclear_matrixCoefficient_eq_zero {ι : Type*} [Countable ι]
    (u v : ι → Schrodinger E) (huv : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hz : ∀ q, nuclearSection u v q = 0) (f g : 𝓢(E,ℂ)) :
    ⟪f.toLp 2 volume, (∑' i, outerOperator (u i) (v i)).1 (g.toLp 2 volume)⟫_ℂ = 0 := by
  let A : ι → E → ℂ := fun i x => star (f x) * u i x
  let B : ι → E → ℂ := fun i x => star (v i x) * g x
  let F : ι → E → ℂ := fun i => correlation (A i) (B i)
  have hA (i) : Integrable (A i) := integrable_schwartz_left f (u i)
  have hB (i) : Integrable (B i) := integrable_schwartz_right g (v i)
  have hF (i) : Integrable (F i) := integrable_correlation (hA i) (hB i)
  have hb (i) : (∫ q, ‖F i q‖) ≤ (‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖) * (‖u i‖ * ‖v i‖) := by
    calc
      _ ≤ (∫ x, ‖A i x‖) * (∫ x, ‖B i x‖) := integral_norm_correlation_le (hA i) (hB i)
      _ ≤ (‖f.toLp 2 volume‖ * ‖u i‖) * (‖v i‖ * ‖g.toLp 2 volume‖) :=
        mul_le_mul (integral_norm_schwartz_left_le f (u i))
          (integral_norm_schwartz_right_le g (v i))
          (integral_nonneg (fun _ => norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hsum : Summable (fun i => ∫ q, ‖F i q‖) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) hb
      (huv.mul_left (‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖))
  have hFzero (q : E) : ∑' i, F i q = 0 := by
    have hs := ((summable_norm_rankOneSection u v huv q).of_norm.hasSum.mapL
      (l1TestFunctional (schwartzTestTop f g q))).tsum_eq
    change (∑' i, l1TestFunctional (schwartzTestTop f g q) (rankOneSection q (u i) (v i))) =
      l1TestFunctional (schwartzTestTop f g q) (nuclearSection u v q) at hs
    simpa only [test_rankOneSection, hz q, map_zero] using hs
  have hi : (∑' i, ⟪f.toLp 2 volume,u i⟫_ℂ * ⟪v i,g.toLp 2 volume⟫_ℂ) = 0 := by
    have h := integral_tsum_of_summable_integral_norm hF hsum
    have hterm i : (∫ q, F i q) = ⟪f.toLp 2 volume,u i⟫_ℂ * ⟪v i,g.toLp 2 volume⟫_ℂ := by
      rw [integral_correlation (hA i) (hB i), integral_schwartz_left, integral_schwartz_right]
    simpa only [hterm, hFzero, integral_zero] using h
  let L : TraceClass (Schrodinger E) →L[ℂ] ℂ := (innerSL ℂ (f.toLp 2 volume)).comp
    ((ContinuousLinearMap.apply ℂ (Schrodinger E) (g.toLp 2 volume)).comp traceClassInclusion)
  have ho : Summable (fun i => outerOperator (u i) (v i)) := by
    apply Summable.of_norm
    simpa only [norm_outerOperator] using huv
  have hs := (ho.hasSum.mapL L).tsum_eq
  have hterm i : L (outerOperator (u i) (v i)) = ⟪f.toLp 2 volume,u i⟫_ℂ * ⟪v i,g.toLp 2 volume⟫_ℂ := by
    change ⟪f.toLp 2 volume,InnerProductSpace.rankOne ℂ (u i) (v i) (g.toLp 2 volume)⟫_ℂ = _
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm]
  simp_rw [hterm] at hs
  rw [hi] at hs
  exact hs.symm

/-- Weyl observables separate all actual trace-class operators in finite configuration dimension. -/
theorem traceClass_eq_zero_of_weyl_zero (T : TraceClass (Schrodinger E))
    (hT : ∀ q p : E, TraceClass.tracePairing (weylOperator q p) T = 0) : T = 0 := by
  obtain ⟨ι,hι,u,v,huv,rfl⟩ := exists_countable_nuclear_expansion T
  letI := hι
  have hz := nuclearSection_eq_zero_of_weyl_zero u v huv hT
  have hm := nuclear_matrixCoefficient_eq_zero u v huv hz
  let T : TraceClass (Schrodinger E) := ∑' i, outerOperator (u i) (v i)
  have hall : ∀ x y : Schrodinger E, ⟪x,T.1 y⟫_ℂ = 0 := by
    intro x y
    refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (by norm_num)).induction_on₂ ?_ ?_ x y
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact hm
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro y
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  simpa using hall (T.1 y) y

/-- Equality of raw Weyl traces determines the actual density, not only its Gaussian parameters. -/
theorem NormalDensity.ext_characteristic {ρ σ : NormalDensity (Schrodinger E)}
    (h : ∀ q p, ρ.characteristic q p = σ.characteristic q p) : ρ = σ := by
  apply NormalDensity.ext
  apply sub_eq_zero.mp
  apply traceClass_eq_zero_of_weyl_zero
  intro q p
  rw [map_sub]
  exact sub_eq_zero.mpr (h q p)

end Gaussian.Physical.Boson
