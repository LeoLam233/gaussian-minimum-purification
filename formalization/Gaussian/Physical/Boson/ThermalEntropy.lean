import Gaussian.Physical.Boson.Thermal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Genuinely summable, extended-valued entropy of the full thermal eigenvalue distribution.
Its identity with general state von Neumann entropy is a separate unclosed bridge. -/
noncomputable section
namespace Gaussian.Physical.Boson
open scoped ENNReal

theorem thermalWeight_le_one {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    thermalWeight r k ≤ 1 := by
  have h := (hasSum_thermalWeight hr).summable.le_tsum k (fun j _ => thermalWeight_nonneg hr j)
  simpa only [(hasSum_thermalWeight hr).tsum_eq] using h

theorem thermalWeight_entropy_nonneg {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    0 ≤ Real.negMulLog (thermalWeight r k) :=
  Real.negMulLog_nonneg (thermalWeight_nonneg hr k) (thermalWeight_le_one hr k)

theorem hasSum_thermalEntropy {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    HasSum (fun k => Real.negMulLog (thermalWeight r k))
      (-Real.log (1-r) - (r/(1-r)) * Real.log r) := by
  by_cases hz : r = 0
  · subst r
    have he : (fun k : ℕ => Real.negMulLog (thermalWeight 0 k)) = 0 := by
      funext k
      cases k <;> simp [thermalWeight]
    rw [he]
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0) using 1; simp
  have hpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
  have h1 : 0 < 1-r := sub_pos.mpr hr.2
  have h := ((hasSum_thermalWeight hr).mul_left (-Real.log (1-r))).sub
    ((hasSum_thermalOccupation hr).mul_right (Real.log r))
  convert h using 1
  · funext k
    rw [Real.negMulLog, thermalWeight, Real.log_mul h1.ne' (pow_pos hpos k).ne', Real.log_pow]
    ring
  · ring

def thermalEigenvalueEntropy (r : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (Real.negMulLog (thermalWeight r k))

theorem thermalEigenvalueEntropy_eq {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    thermalEigenvalueEntropy r =
      ENNReal.ofReal (-Real.log (1-r) - (r/(1-r)) * Real.log r) := by
  rw [thermalEigenvalueEntropy, ← ENNReal.ofReal_tsum_of_nonneg
    (thermalWeight_entropy_nonneg hr) (hasSum_thermalEntropy hr).summable,
    (hasSum_thermalEntropy hr).tsum_eq]

theorem thermalEigenvalueEntropy_ne_top {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    thermalEigenvalueEntropy r ≠ ∞ := by
  rw [thermalEigenvalueEntropy_eq hr]
  exact ENNReal.ofReal_ne_top

def thermalRatio (ν : ℝ) : ℝ := (ν-1)/(ν+1)

theorem thermalRatio_mem {ν : ℝ} (hν : 1 ≤ ν) : thermalRatio ν ∈ Set.Ico (0:ℝ) 1 := by
  have hd : 0 < ν+1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hν) hd.le
  · change (ν-1)/(ν+1) < 1
    rw [div_lt_one hd]
    linarith

theorem thermalEntropy_eq_boson {ν : ℝ} (hν : 1 ≤ ν) :
    -Real.log (1-thermalRatio ν) - (thermalRatio ν/(1-thermalRatio ν)) *
      Real.log (thermalRatio ν) = Gaussian.Entropy.boson ν := by
  by_cases hz : ν = 1
  · subst ν; norm_num [thermalRatio]
  have hpos : 1 < ν := lt_of_le_of_ne hν (Ne.symm hz)
  have hdm : 0 < ν-1 := by linarith
  have hdp : 0 < ν+1 := by linarith
  have he1 : 1-thermalRatio ν = 2/(ν+1) := by unfold thermalRatio; field_simp; ring
  have he2 : thermalRatio ν/(1-thermalRatio ν) = (ν-1)/2 := by
    rw [he1]; unfold thermalRatio; field_simp
  rw [he2, he1, thermalRatio, Gaussian.Entropy.boson, Real.negMulLog, Real.negMulLog,
    Real.log_div (by norm_num : (2:ℝ) ≠ 0) hdp.ne',
    Real.log_div hdm.ne' hdp.ne', Real.log_div hdm.ne' (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div hdp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  ring

theorem thermalEigenvalueEntropy_eq_boson {ν : ℝ} (hν : 1 ≤ ν) :
    thermalEigenvalueEntropy (thermalRatio ν) = ENNReal.ofReal (Gaussian.Entropy.boson ν) := by
  rw [thermalEigenvalueEntropy_eq (thermalRatio_mem hν), thermalEntropy_eq_boson hν]

end Gaussian.Physical.Boson
