import Gaussian.Attainment.BosonicCost
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Explicit separation of Frobenius matrix norm and induced Hilbert operator norm.
Frobenius domination is proved by explicit matrix-column multiplication; the
two norms are never silently identified. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Attainment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Frobenius domination of the genuine Euclidean operator norm, proved using
matrix-column multiplication rather than an implicit matrix norm conversion. -/
theorem operator_norm_le_frobenius (A : HermitianMat ι ℂ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A.mat‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  let C : Matrix ι Unit ℂ := Matrix.replicateCol Unit (WithLp.ofLp x)
  have hc : A.mat * C = Matrix.replicateCol Unit (A.mat *ᵥ WithLp.ofLp x) := by
    ext i j
    rfl
  have hm := Matrix.frobenius_norm_mul A.mat C
  rw [hc, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at hm
  have hA : @norm _ (Matrix.frobeniusSeminormedAddCommGroup : SeminormedAddCommGroup (Matrix ι ι ℂ)).toNorm A.mat = ‖A‖ := by
    rw [Matrix.frobenius_norm_def, HermitianMat.norm_eq_frobenius]
    simp only [Real.rpow_two, HermitianMat.mat_apply]
  rw [hA, WithLp.toLp_ofLp] at hm
  simpa only [← Matrix.toEuclideanCLM_toLp, WithLp.toLp_ofLp] using hm

theorem frobenius_bound_of_spectral_bound (A : HermitianMat ι ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hA : ∀ i, |A.H.eigenvalues i| ≤ B) :
    ‖A‖ ≤ Real.sqrt (Fintype.card ι) * B := by
  have hs : ‖A‖^2 ≤ (Fintype.card ι : ℝ) * B^2 := by
    rw [HermitianMat.norm_eq_sum_eigenvalues_sq]
    calc
      ∑ i, A.H.eigenvalues i ^ 2 ≤ ∑ _i : ι, B^2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := (sq_le_sq₀ (abs_nonneg _) hB).mpr (hA i)
        simpa only [sq_abs] using h
      _ = _ := by simp
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsqrt := Real.sq_sqrt hn
  have hpos := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  nlinarith [norm_nonneg A, mul_nonneg hpos hB]

/-- Every sublevel of the continuous extended bosonic spectral functional has a
uniform induced operator-norm bound. Physical uncertainty is not needed here. -/
theorem exists_bosonHermitianCost_operator_bound (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ A : HermitianMat ι ℂ, bosonHermitianCost A ≤ C →
      ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A.mat‖ ≤ B := by
  obtain ⟨β,hβ,hfloor⟩ := Gaussian.Entropy.exists_boson_lower_bound
  let D := max 1 (2 * Real.exp (2*C+(Fintype.card ι : ℝ)*β)-1)
  have hD : 0 ≤ D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨Real.sqrt (Fintype.card ι) * D + 1,by positivity,?_⟩
  intro A hC
  have heig : ∀ i, |A.H.eigenvalues i| ≤ D := by
    intro i
    have hs : Gaussian.Entropy.boson |A.H.eigenvalues i| + β ≤
        ∑ j, (Gaussian.Entropy.boson |A.H.eigenvalues j| + β) := by
      apply Finset.single_le_sum _ (Finset.mem_univ i)
      intro j _
      have h := hfloor |A.H.eigenvalues j| (abs_nonneg _)
      linarith
    rw [Finset.sum_add_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hc : Gaussian.Entropy.boson |A.H.eigenvalues i| ≤
        2*C+(Fintype.card ι : ℝ)*β := by
      rw [bosonHermitianCost_eq] at hC
      linarith
    exact Gaussian.Entropy.boson_parameter_bound_nonnegative (abs_nonneg _) hc
  exact (operator_norm_le_frobenius A).trans
    ((frobenius_bound_of_spectral_bound A hD heig).trans (by linarith))
end Gaussian.Attainment
