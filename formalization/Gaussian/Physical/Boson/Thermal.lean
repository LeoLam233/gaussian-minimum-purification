import Gaussian.Physical.Boson.NormalDensity
import Gaussian.Entropy.Scalar
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual full-occupation thermal densities and eigenvectors. Gaussian Weyl classification is not assumed. -/
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace lp

abbrev OccupationHilbert (n : ℕ) := ℓ²((Fin n → ℕ), ℂ)

def occupationBasis (n : ℕ) : HilbertBasis (Fin n → ℕ) ℂ (OccupationHilbert n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem normalMixture_eigenvector {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (b : HilbertBasis ι ℂ H) (j : ι) :
    (normalMixture p hp hs b b.orthonormal.norm_eq_one).operator.1 (b j) = (p j : ℂ) • b j := by
  classical
  let ev : TraceClass H →L[ℂ] H := (ContinuousLinearMap.apply ℂ H (b j)).comp traceClassInclusion
  have he := ev.map_tsum (summable_weighted_vectorOperator p hp hs.summable b b.orthonormal.norm_eq_one)
  change (normalMixture p hp hs b b.orthonormal.norm_eq_one).operator.1 (b j) = _ at he
  rw [he, tsum_eq_single j]
  · change ((p j : ℂ) • InnerProductSpace.rankOne ℂ (b j) (b j)) (b j) = _
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  · intro i hij
    change ((p i : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i)) (b j) = 0
    simp [InnerProductSpace.rankOne_apply, b.orthonormal.inner_eq_zero hij]

def thermalWeight (r : ℝ) (k : ℕ) : ℝ := (1-r) * r^k

theorem thermalWeight_nonneg {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    0 ≤ thermalWeight r k := mul_nonneg (sub_nonneg.mpr hr.2.le) (pow_nonneg hr.1 _)

theorem hasSum_thermalWeight {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    HasSum (thermalWeight r) 1 := by
  have h := (hasSum_geometric_of_lt_one hr.1 hr.2).mul_left (1-r)
  change HasSum (fun k : ℕ => (1-r) * r^k) 1
  simpa only [mul_inv_cancel₀ (sub_ne_zero.mpr hr.2.ne')] using h

def thermalDensity (r : ℝ) (hr : r ∈ Set.Ico (0:ℝ) 1) : NormalDensity ℓ²(ℕ, ℂ) :=
  normalMixture (thermalWeight r) (thermalWeight_nonneg hr) (hasSum_thermalWeight hr)
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _))
    (HilbertBasis.orthonormal _).norm_eq_one

theorem thermalDensity_eigenvector (r : ℝ) (hr : r ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    (thermalDensity r hr).operator.1 (lp.single 2 k (1:ℂ)) =
      (thermalWeight r k : ℂ) • lp.single 2 k (1:ℂ) := by
  let b : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : b k = lp.single 2 k (1:ℂ) := b.repr_self k
  rw [← hb]
  exact normalMixture_eigenvector (thermalWeight r) (thermalWeight_nonneg hr)
    (hasSum_thermalWeight hr) b k

theorem hasSum_thermalOccupation {r : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) :
    HasSum (fun k : ℕ => (k:ℝ) * thermalWeight r k) (r/(1-r)) := by
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (1-r)
  convert h using 1
  · funext k; unfold thermalWeight; ring
  · field_simp

end Gaussian.Physical.Boson
