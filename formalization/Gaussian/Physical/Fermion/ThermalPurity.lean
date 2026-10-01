import Gaussian.Physical.Fermion.ThermalGaussian
import Gaussian.Physical.Fermion.ParityEndpoints

/-! Actual purity of the canonical and rotated thermal densities, with both
signed pure endpoints and the empty system included. -/
noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion

theorem ofClassical_constant_pure {d : Type*} [Fintype d] [DecidableEq d] (a : d) :
    MState.ofClassical (ProbDistribution.constant a) = MState.pure (Ket.basis a) := by
  apply MState.ext_m
  change Matrix.diagonal (fun i => ((ProbDistribution.constant a i : ℝ) : ℂ)) = _
  ext i j
  by_cases hi : a=i <;> by_cases hj : a=j <;> by_cases hij : i=j <;>
    simp_all [Matrix.diagonal_apply,ProbDistribution.constant,MState.pure_apply,Ket.basis,Ket.apply]

theorem thermal_pure_of_endpoints (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (he : ∀ i, t i=1 ∨ t i = -1) :
    ∃ ψ, thermal n t ht = MState.pure ψ := by
  induction n with
  | zero => exact ⟨Ket.basis (),ofClassical_constant_pure ()⟩
  | succ n ih =>
    obtain ⟨φ,hφ⟩ := ih (fun i => t i.succ) (fun i => ht i.succ) (fun i => he i.succ)
    have hfirst : ∃ ξ, oneThermal (t 0) (ht 0) = MState.pure ξ := by
      rcases he 0 with hp | hm
      · refine ⟨Ket.basis false,?_⟩
        simpa only [hp] using oneThermal_positive_endpoint (by norm_num)
      · refine ⟨Ket.basis true,?_⟩
        simpa only [hm] using oneThermal_negative_endpoint (by norm_num)
    obtain ⟨ξ,hξ⟩ := hfirst
    refine ⟨ξ.prod φ,?_⟩
    rw [thermal,hξ,hφ,MState.pure_prod_pure]

theorem fermion_scalar_neg (t : ℝ) : Gaussian.Entropy.fermion (-t) = Gaussian.Entropy.fermion t := by
  unfold Gaussian.Entropy.fermion
  simp only [sub_neg_eq_add,← sub_eq_add_neg]
  exact add_comm _ _

theorem fermion_scalar_abs (t : ℝ) : Gaussian.Entropy.fermion |t| = Gaussian.Entropy.fermion t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht,fermion_scalar_neg]

theorem fermion_scalar_signed_nonneg (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    0 ≤ Gaussian.Entropy.fermion t := by
  rw [← fermion_scalar_abs]
  exact Gaussian.Entropy.fermion_nonneg ⟨abs_nonneg t,abs_le.mpr ht⟩

theorem fermion_scalar_signed_eq_zero_iff (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Gaussian.Entropy.fermion t = 0 ↔ t=1 ∨ t = -1 := by
  rw [← fermion_scalar_abs,Gaussian.Entropy.fermion_eq_zero_iff ⟨abs_nonneg t,abs_le.mpr ht⟩]
  have h : (1:ℝ) = |(1:ℝ)| := by norm_num
  rw [h,abs_eq_abs]
  norm_num

/-- Actual pure thermal densities are exactly those with pure signed covariance endpoints. -/
theorem thermal_pure_iff_endpoints (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) :
    (∃ ψ, thermal n t ht = MState.pure ψ) ↔ ∀ i, t i=1 ∨ t i = -1 := by
  constructor
  · rintro ⟨ψ,hψ⟩
    have hsum : ∑ i, Gaussian.Entropy.fermion (t i) = 0 := by
      rw [← entropy_thermal n t ht,hψ,Sᵥₙ_of_pure_zero]
    intro i
    apply (fermion_scalar_signed_eq_zero_iff (t i) (ht i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => fermion_scalar_signed_nonneg (t j) (ht j))).mp hsum i (by simp)
  · exact thermal_pure_of_endpoints n t ht

/-- The same criterion is actual pure-quasifree admissibility, with no parity-sign exclusion. -/
theorem thermal_isPureQuasifree_iff_endpoints (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) :
    IsPureQuasifree (thermal n t ht) ↔ ∀ i, t i=1 ∨ t i = -1 := by
  constructor
  · intro h
    exact (thermal_pure_iff_endpoints n t ht).mp h.2
  · intro h
    exact ⟨thermal_isQuasifree n t ht,(thermal_pure_iff_endpoints n t ht).mpr h⟩

end Gaussian.Physical.Fermion
