import Gaussian.Physical.Boson.ProductWeights
import Gaussian.Physical.Boson.DiagonalEntropy
import Gaussian.Physical.Boson.PureEntropy

/-! Actual full finite-mode diagonal thermal densities and their canonical CFC entropy.
The generic Hilbert-basis version is usable directly on a Schrödinger product basis.
No Weyl/Gaussian interpretation is assumed by this spectral construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ENNReal InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The full, untruncated thermal product density on any actual occupation-indexed Hilbert basis. -/
def thermalProductDensity {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) : NormalDensity H :=
  normalMixture (occupationThermalWeight ν) (occupationThermalWeight_nonneg ν hν)
    (hasSum_occupationThermalWeight ν hν) b b.orthonormal.norm_eq_one

theorem thermalProductDensity_eigenvector {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) (k : Fin n → ℕ) :
    (thermalProductDensity b ν hν).operator.1 (b k) = (occupationThermalWeight ν k : ℂ) • b k :=
  normalMixture_eigenvector _ _ _ b k

/-- The entropy is canonical CFC von Neumann entropy of this actual normal density. -/
theorem thermalProductDensity_entropy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (thermalProductDensity b ν hν).entropy = ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) := by
  rw [NormalDensity.entropy_eq_diagonal_sum _ b (occupationThermalWeight ν)
    (fun k => ⟨occupationThermalWeight_nonneg ν hν k, occupationThermalWeight_le_one ν hν k⟩)
    (thermalProductDensity_eigenvector b ν hν) (hasSum_occupationThermalEntropy ν hν).summable,
    (hasSum_occupationThermalEntropy ν hν).tsum_eq]

theorem thermalProductDensity_entropy_ne_top {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) : (thermalProductDensity b ν hν).entropy ≠ ⊤ := by
  rw [thermalProductDensity_entropy]
  exact ENNReal.ofReal_ne_top

theorem thermalProductDensity_entropy_toReal {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (thermalProductDensity b ν hν).entropy.toReal = ∑ i, Gaussian.Entropy.boson (ν i) := by
  rw [thermalProductDensity_entropy, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun i _ => Gaussian.Entropy.boson_nonneg (hν i))

lemma occupationThermalWeight_pure_zero {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, ν i = 1) :
    occupationThermalWeight ν 0 = 1 := by
  simp [occupationThermalWeight, hν, thermalRatio, thermalWeight]

lemma occupationThermalWeight_pure_nonzero {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, ν i = 1)
    (k : Fin n → ℕ) (hk : k ≠ 0) : occupationThermalWeight ν k = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  unfold occupationThermalWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hν i, thermalRatio, thermalWeight, zero_pow hi]

/-- All-pure parameters give a genuine rank-one vacuum, including the empty product. -/
theorem thermalProductDensity_eq_vacuum {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) (hp : ∀ i, ν i = 1) :
    thermalProductDensity b ν hν = vectorDensity (b 0) (b.orthonormal.norm_eq_one 0) := by
  apply NormalDensity.ext
  change (∑' k, (occupationThermalWeight ν k : ℂ) • vectorOperator (b k)) = vectorOperator (b 0)
  rw [tsum_eq_single 0]
  · rw [occupationThermalWeight_pure_zero ν hp]
    simp
  · intro k hk
    rw [occupationThermalWeight_pure_nonzero ν hp k hk]
    simp

/-- Actual purity is equivalent to all thermal parameters being the exact pure endpoint. -/
theorem thermalProductDensity_isPure_iff {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (thermalProductDensity b ν hν).IsPure ↔ ∀ i, ν i = 1 := by
  constructor
  · intro hp
    have he : ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) = 0 := by
      rw [← thermalProductDensity_entropy b ν hν, hp.entropy_eq_zero]
    have hs : (∑ i, Gaussian.Entropy.boson (ν i)) = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp he)
        (Finset.sum_nonneg (fun i _ => Gaussian.Entropy.boson_nonneg (hν i)))
    intro i
    apply (Gaussian.Entropy.boson_eq_zero_iff (hν i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Gaussian.Entropy.boson_nonneg (hν j))).mp hs i (Finset.mem_univ i)
  · intro hp
    rw [thermalProductDensity_eq_vacuum b ν hν hp]
    exact vectorDensity_isPure _ _

/-- Specialization to the full bosonic occupation Hilbert space. -/
def occupationThermalDensity {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    NormalDensity (OccupationHilbert n) := thermalProductDensity (occupationBasis n) ν hν

theorem occupationThermalDensity_entropy {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (occupationThermalDensity ν hν).entropy = ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) :=
  thermalProductDensity_entropy (occupationBasis n) ν hν

theorem occupationThermalDensity_isPure_iff {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (occupationThermalDensity ν hν).IsPure ↔ ∀ i, ν i = 1 :=
  thermalProductDensity_isPure_iff (occupationBasis n) ν hν

end Gaussian.Physical.Boson
