import Gaussian.Physical.Boson.CFCEigenvector
import Gaussian.Physical.Boson.ThermalEntropy
import Gaussian.Physical.Boson.OscillatorBasis

/-! Canonical CFC entropy of genuine infinite-dimensional diagonal normal densities. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped InnerProductSpace ENNReal lp
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weightedBasisOperator (p : ι → ℝ) (b : HilbertBasis ι ℂ H) : TraceClass H :=
  ∑' i, (p i : ℂ) • vectorOperator (b i)

theorem weightedBasisOperator_eigenvector (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (b : HilbertBasis ι ℂ H) (j : ι) :
    (weightedBasisOperator p b).1 (b j) = (p j : ℂ) • b j := by
  classical
  let ev : TraceClass H →L[ℂ] H := (ContinuousLinearMap.apply ℂ H (b j)).comp traceClassInclusion
  have he := ev.map_tsum (summable_weighted_vectorOperator p hp hs b b.orthonormal.norm_eq_one)
  change (weightedBasisOperator p b).1 (b j) = _ at he
  rw [he, tsum_eq_single j]
  · change ((p j : ℂ) • InnerProductSpace.rankOne ℂ (b j) (b j)) (b j) = _
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  · intro i hij
    change ((p i : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i)) (b j) = 0
    simp [InnerProductSpace.rankOne_apply, b.orthonormal.inner_eq_zero hij]

theorem normalTrace_weightedBasisOperator (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (b : HilbertBasis ι ℂ H) :
    normalTrace (weightedBasisOperator p b) = (∑' i, p i : ℝ) := by
  rw [weightedBasisOperator, normalTrace.map_tsum
    (summable_weighted_vectorOperator p hp hs b b.orthonormal.norm_eq_one)]
  simpa only [map_smul, normalTrace_vectorOperator, b.orthonormal.norm_eq_one,
    one_pow, Complex.ofReal_one, smul_eq_mul, mul_one] using
    (Complex.hasSum_ofReal.mpr hs.hasSum).tsum_eq

theorem NormalDensity.entropyOperator_eq_weightedBasis (ρ : NormalDensity H)
    (b : HilbertBasis ι ℂ H) (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (he : ∀ i, ρ.operator.1 (b i) = (p i : ℂ) • b i)
    (hs : Summable (fun i => Real.negMulLog (p i))) :
    ρ.entropyOperator = (weightedBasisOperator (fun i => Real.negMulLog (p i)) b).1 := by
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i,rfl⟩
  rw [weightedBasisOperator_eigenvector _ (fun i => Real.negMulLog_nonneg (hp i).1 (hp i).2) hs]
  exact cfc_apply_eigenvector ρ.operator.1 (.of_nonneg ρ.nonneg) (p i) (b i)
    (b.orthonormal.ne_zero i) (he i) _ Real.continuous_negMulLog

theorem NormalDensity.entropy_eq_diagonal_sum (ρ : NormalDensity H)
    (b : HilbertBasis ι ℂ H) (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (he : ∀ i, ρ.operator.1 (b i) = (p i : ℂ) • b i)
    (hs : Summable (fun i => Real.negMulLog (p i))) :
    ρ.entropy = ENNReal.ofReal (∑' i, Real.negMulLog (p i)) := by
  have hOp := ρ.entropyOperator_eq_weightedBasis b p hp he hs
  have hTC : IsTraceClass ρ.entropyOperator := hOp ▸ (weightedBasisOperator _ b).2
  rw [ρ.entropy_eq_of_traceClass hTC]
  have ht := TraceClass.trace_transport hOp hTC
  rw [ht]
  change ENNReal.ofReal (normalTrace (weightedBasisOperator _ b)).re = _
  rw [normalTrace_weightedBasisOperator _ (fun i => Real.negMulLog_nonneg (hp i).1 (hp i).2) hs]
  rfl

theorem thermalDensity_entropy {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    (thermalDensity r hr).entropy = thermalEigenvalueEntropy r := by
  let b : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  rw [NormalDensity.entropy_eq_diagonal_sum (thermalDensity r hr) b (thermalWeight r)
    (fun i => ⟨thermalWeight_nonneg hr i, thermalWeight_le_one hr i⟩)
    (fun i => normalMixture_eigenvector _ _ _ b i) (hasSum_thermalEntropy hr).summable]
  rw [thermalEigenvalueEntropy_eq hr, (hasSum_thermalEntropy hr).tsum_eq]

theorem thermalDensity_entropy_eq_boson {ν : ℝ} (hν : 1 ≤ ν) :
    (thermalDensity (thermalRatio ν) (thermalRatio_mem hν)).entropy =
      ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  rw [thermalDensity_entropy, thermalEigenvalueEntropy_eq_boson hν]

theorem schrodingerThermalDensity_entropy_eq_boson
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) {ν : ℝ} (hν : 1 ≤ ν) :
    (schrodingerThermalDensity Q (thermalRatio ν) (thermalRatio_mem hν)).entropy =
      ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  unfold schrodingerThermalDensity
  rw [NormalDensity.entropy_eq_diagonal_sum _ (oscillatorBasis Q) (thermalWeight (thermalRatio ν))
    (fun i => ⟨thermalWeight_nonneg (thermalRatio_mem hν) i,
      thermalWeight_le_one (thermalRatio_mem hν) i⟩)
    (fun i => normalMixture_eigenvector _ _ _ (oscillatorBasis Q) i)
    (hasSum_thermalEntropy (thermalRatio_mem hν)).summable,
    (hasSum_thermalEntropy (thermalRatio_mem hν)).tsum_eq, thermalEntropy_eq_boson hν]

end Gaussian.Physical.Boson
