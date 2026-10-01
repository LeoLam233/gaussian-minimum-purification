import Gaussian.Physical.Boson.ThermalEntropy
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic

/-! Absolutely summable finite occupation-product weights and entropy, including zero modes.
The entropy identity is proved from the actual probability weights, not stipulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson

/-- Finite products of absolutely summable scalar sequences, indexed by full occupation tuples. -/
theorem hasSum_fin_product {𝕜 : Type*} [NormedCommRing 𝕜] [NormedSpace ℝ 𝕜]
    [FiniteDimensional ℝ 𝕜] [CompleteSpace 𝕜]
    {n : ℕ} (f : Fin n → ℕ → 𝕜) (a : Fin n → 𝕜)
    (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun k : Fin n → ℕ => ∏ i, f i (k i)) (∏ i, a i) := by
  classical
  induction n with
  | zero =>
      simpa using (hasSum_fintype (fun _ : Fin 0 → ℕ => (1:𝕜)))
  | succ n ih =>
      have ht := ih (fun i : Fin n => f i.succ) (fun i : Fin n => a i.succ) (fun i : Fin n => hf i.succ)
      have hn0 : Summable (fun k : ℕ => ‖f 0 k‖) := (hf 0).summable.norm
      have hnt : Summable (fun k : Fin n → ℕ => ‖∏ i : Fin n, f i.succ (k i)‖) := ht.summable.norm
      have hprod : Summable (fun k : ℕ × (Fin n → ℕ) => f 0 k.1 * ∏ i : Fin n, f i.succ (k.2 i)) :=
        summable_mul_of_summable_norm (f := f 0) (g := fun k : Fin n → ℕ => ∏ i : Fin n, f i.succ (k i)) hn0 hnt
      have h := (hf 0).mul ht hprod
      apply (Fin.consEquiv (fun _ : Fin (n+1) => ℕ)).hasSum_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using h

/-- Entropy of a countable product distribution; zeros and pure endpoints are included. -/
theorem hasSum_product_entropy {ι κ : Type*} {p : ι → ℝ} {q : κ → ℝ} {s t : ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hs : HasSum (fun i => Real.negMulLog (p i)) s)
    (ht : HasSum (fun j => Real.negMulLog (q j)) t) :
    HasSum (fun k : ι × κ => Real.negMulLog (p k.1 * q k.2)) (s+t) := by
  have h1 := hs.mul hq (summable_mul_of_summable_norm hs.summable.norm hq.summable.norm)
  have h2 := hp.mul ht (summable_mul_of_summable_norm hp.summable.norm ht.summable.norm)
  convert h1.add h2 using 1
  · funext k
    rw [Real.negMulLog_mul]
    ring
  · ring

/-- Summable entropy of every finite independent countable probability family. -/
theorem hasSum_fin_product_entropy {n : ℕ} (p : Fin n → ℕ → ℝ) (s : Fin n → ℝ)
    (hp : ∀ i, HasSum (p i) 1)
    (hs : ∀ i, HasSum (fun k => Real.negMulLog (p i k)) (s i)) :
    HasSum (fun k : Fin n → ℕ => Real.negMulLog (∏ i, p i (k i))) (∑ i, s i) := by
  classical
  induction n with
  | zero =>
      simpa using (hasSum_zero : HasSum (fun _ : Fin 0 → ℕ => (0:ℝ)) 0)
  | succ n ih =>
      have ht := ih (fun i : Fin n => p i.succ) (fun i : Fin n => s i.succ)
        (fun i : Fin n => hp i.succ) (fun i : Fin n => hs i.succ)
      have hp' : HasSum (fun k : Fin n → ℕ => ∏ i : Fin n, p i.succ (k i)) 1 := by
        simpa using hasSum_fin_product (fun i : Fin n => p i.succ) (fun _ => (1:ℝ)) (fun i : Fin n => hp i.succ)
      have h := hasSum_product_entropy (hp 0) hp' (hs 0) ht
      apply (Fin.consEquiv (fun _ : Fin (n+1) => ℕ)).hasSum_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using h

/-- The actual full occupation weight for finitely many thermal modes. -/
def occupationThermalWeight {n : ℕ} (ν : Fin n → ℝ) (k : Fin n → ℕ) : ℝ :=
  ∏ i, thermalWeight (thermalRatio (ν i)) (k i)

lemma occupationThermalWeight_nonneg {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (k : Fin n → ℕ) : 0 ≤ occupationThermalWeight ν k :=
  Finset.prod_nonneg (fun i _ => thermalWeight_nonneg (thermalRatio_mem (hν i)) (k i))

theorem hasSum_occupationThermalWeight {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    HasSum (occupationThermalWeight ν) 1 := by
  change HasSum (fun k : Fin n → ℕ => ∏ i, thermalWeight (thermalRatio (ν i)) (k i)) 1
  simpa only [Finset.prod_const_one] using
    hasSum_fin_product (fun i => thermalWeight (thermalRatio (ν i))) (fun _ => (1:ℝ))
      (fun i => hasSum_thermalWeight (thermalRatio_mem (hν i)))

lemma occupationThermalWeight_le_one {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (k : Fin n → ℕ) : occupationThermalWeight ν k ≤ 1 := by
  have h := (hasSum_occupationThermalWeight ν hν).summable.le_tsum k
    (fun j _ => occupationThermalWeight_nonneg ν hν j)
  simpa only [(hasSum_occupationThermalWeight ν hν).tsum_eq] using h

/-- Exact finite-mode spectral entropy with a proved HasSum, valid at all pure/mixed endpoints. -/
theorem hasSum_occupationThermalEntropy {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    HasSum (fun k => Real.negMulLog (occupationThermalWeight ν k))
      (∑ i, Gaussian.Entropy.boson (ν i)) := by
  apply hasSum_fin_product_entropy
  · intro i
    exact hasSum_thermalWeight (thermalRatio_mem (hν i))
  · intro i
    simpa only [thermalEntropy_eq_boson (hν i)] using hasSum_thermalEntropy (thermalRatio_mem (hν i))

end Gaussian.Physical.Boson
