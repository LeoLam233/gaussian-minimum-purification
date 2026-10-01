import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Pairing
import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.RankOne
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Genuine normal densities on arbitrary complete complex Hilbert spaces.
No covariance realization, Gaussianity, entropy or restriction bridge is assumed as a field. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def traceClassInclusion : TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := fun T => T.1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : TraceClass H →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous 1
    (fun T => by
      change ‖T.1‖ ≤ 1 * ‖T‖
      rw [one_mul, TraceClass.norm_eq_traceNorm]
      exact opNorm_le_traceNorm (TraceClass.isTraceClass_coe T))

@[simp] theorem traceClassInclusion_apply (T : TraceClass H) :
    traceClassInclusion T = T.1 := rfl

def normalTrace : TraceClass H →L[ℂ] ℂ := TraceClass.tracePairing 1

@[simp] theorem normalTrace_apply (T : TraceClass H) :
    normalTrace T = trace T.1 (TraceClass.isTraceClass_coe T) := by
  simp only [normalTrace, TraceClass.tracePairing_apply, one_mul]

structure NormalDensity (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : TraceClass H
  nonneg : 0 ≤ operator.1
  trace_one : normalTrace operator = 1

namespace NormalDensity

def expect (ρ : NormalDensity H) (A : H →L[ℂ] H) : ℂ :=
  TraceClass.tracePairing A ρ.operator

@[simp] theorem expect_one (ρ : NormalDensity H) : ρ.expect 1 = 1 := ρ.trace_one

theorem ext {ρ σ : NormalDensity H} (h : ρ.operator = σ.operator) : ρ = σ := by
  cases ρ; cases σ; cases h; rfl

end NormalDensity

def vectorOperator (x : H) : TraceClass H :=
  TraceClass.ofOperator (InnerProductSpace.rankOne ℂ x x) (isTraceClass_rankOne_self x)

@[simp] theorem vectorOperator_coe (x : H) :
    (vectorOperator x).1 = InnerProductSpace.rankOne ℂ x x := rfl

@[simp] theorem norm_vectorOperator (x : H) : ‖vectorOperator x‖ = ‖x‖ ^ 2 :=
  traceNorm_rankOne_self x

@[simp] theorem normalTrace_vectorOperator (x : H) :
    normalTrace (vectorOperator x) = (‖x‖ ^ 2 : ℝ) := by
  simpa only [normalTrace_apply, vectorOperator_coe] using trace_rankOne_self x

def vectorDensity (x : H) (hx : ‖x‖ = 1) : NormalDensity H where
  operator := vectorOperator x
  nonneg := (InnerProductSpace.rankOne ℂ x x).nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self x)
  trace_one := by rw [normalTrace_vectorOperator, hx]; norm_num

def NormalDensity.IsPure (ρ : NormalDensity H) : Prop :=
  ∃ x : H, ∃ hx : ‖x‖ = 1, ρ = vectorDensity x hx

theorem vectorDensity_isPure (x : H) (hx : ‖x‖ = 1) :
    (vectorDensity x hx).IsPure := ⟨x, hx, rfl⟩

theorem summable_weighted_vectorOperator {ι : Type*} (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (v : ι → H) (hv : ∀ i, ‖v i‖ = 1) :
    Summable (fun i => (p i : ℂ) • vectorOperator (v i)) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_vectorOperator, hv, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)] using hs

def normalMixture {ι : Type*} (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : HasSum p 1) (v : ι → H) (hv : ∀ i, ‖v i‖ = 1) : NormalDensity H where
  operator := ∑' i, (p i : ℂ) • vectorOperator (v i)
  nonneg := by
    have hc := traceClassInclusion.map_tsum (summable_weighted_vectorOperator p hp hs.summable v hv)
    rw [traceClassInclusion_apply] at hc
    rw [hc]
    apply tsum_nonneg
    intro i
    change 0 ≤ (p i : ℂ) • InnerProductSpace.rankOne ℂ (v i) (v i)
    exact smul_nonneg (by exact_mod_cast hp i)
      ((InnerProductSpace.rankOne ℂ (v i) (v i)).nonneg_iff_isPositive.mpr
        (InnerProductSpace.isPositive_rankOne_self (v i)))
  trace_one := by
    rw [normalTrace.map_tsum (summable_weighted_vectorOperator p hp hs.summable v hv)]
    simpa only [map_smul, normalTrace_vectorOperator, hv, one_pow, Complex.ofReal_one,
      smul_eq_mul, mul_one] using (Complex.hasSum_ofReal.mpr hs).tsum_eq

theorem trace_unitary_conjugate (T : TraceClass H) (U : unitary (H →L[ℂ] H)) :
    trace ((U : H →L[ℂ] H) * T.1 * star (U : H →L[ℂ] H))
      (isTraceClass_mul_mul T.2) = normalTrace T := by
  have hTU : IsTraceClass (T.1 * star (U : H →L[ℂ] H)) := by
    simpa using (isTraceClass_mul_mul (A := 1) (B := star (U : H →L[ℂ] H)) T.2)
  have hc := trace_mul_cycle (A := (U : H →L[ℂ] H)) hTU
  have he : T.1 * star (U : H →L[ℂ] H) * (U : H →L[ℂ] H) = T.1 := by
    rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  calc
    trace ((U : H →L[ℂ] H) * T.1 * star (U : H →L[ℂ] H)) _ =
      trace ((U : H →L[ℂ] H) * (T.1 * star (U : H →L[ℂ] H))) _ :=
        TraceClass.trace_transport (mul_assoc _ _ _) _
    _ = trace (T.1 * star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) _ := hc
    _ = normalTrace T := (TraceClass.trace_transport he _).trans (normalTrace_apply T).symm

def NormalDensity.conjugate (ρ : NormalDensity H) (U : unitary (H →L[ℂ] H)) :
    NormalDensity H where
  operator := TraceClass.ofOperator ((U : H →L[ℂ] H) * ρ.operator.1 * star (U : H →L[ℂ] H))
    (isTraceClass_mul_mul ρ.operator.2)
  nonneg := star_right_conjugate_nonneg ρ.nonneg _
  trace_one := (trace_unitary_conjugate ρ.operator U).trans ρ.trace_one

theorem NormalDensity.conjugate_eigenvector (ρ : NormalDensity H)
    (U : unitary (H →L[ℂ] H)) {x : H} {c : ℂ} (hx : ρ.operator.1 x = c • x) :
    (ρ.conjugate U).operator.1 ((U : H →L[ℂ] H) x) = c • (U : H →L[ℂ] H) x := by
  change ((U : H →L[ℂ] H) * ρ.operator.1 * star (U : H →L[ℂ] H))
    ((U : H →L[ℂ] H) x) = _
  have he : star (U : H →L[ℂ] H) ((U : H →L[ℂ] H) x) = x := by
    change (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) x = x
    rw [Unitary.coe_star_mul_self]; rfl
  simp only [mul_apply_eq_comp, he, hx, map_smul]

theorem vectorDensity_expect (x : H) (hx : ‖x‖ = 1) (A : H →L[ℂ] H) :
    (vectorDensity x hx).expect A = ⟪x, A x⟫_ℂ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  unfold NormalDensity.expect
  rw [TraceClass.tracePairing_apply, trace_eq_of_hilbertBasis _ b]
  simpa only [vectorDensity, vectorOperator_coe, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right] using
    b.tsum_inner_mul_inner x (A x)

theorem conjugate_vectorDensity (x : H) (hx : ‖x‖ = 1)
    (U : unitary (H →L[ℂ] H)) :
    (vectorDensity x hx).conjugate U =
      vectorDensity ((U : H →L[ℂ] H) x) ((Unitary.norm_map U x).trans hx) := by
  apply NormalDensity.ext
  apply Subtype.ext
  ext y
  change ((U : H →L[ℂ] H) * InnerProductSpace.rankOne ℂ x x * star (U : H →L[ℂ] H)) y =
    InnerProductSpace.rankOne ℂ ((U : H →L[ℂ] H) x) ((U : H →L[ℂ] H) x) y
  simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem NormalDensity.IsPure.conjugate {ρ : NormalDensity H} (hρ : ρ.IsPure)
    (U : unitary (H →L[ℂ] H)) : (ρ.conjugate U).IsPure := by
  obtain ⟨x, hx, rfl⟩ := hρ
  rw [conjugate_vectorDensity]
  exact vectorDensity_isPure _ _

end Gaussian.Physical.Boson
