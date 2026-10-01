import Gaussian.Physical.Fermion.TwoPoint
import Gaussian.Entropy.Scalar

noncomputable section
open scoped Matrix Kronecker BigOperators MState
namespace Gaussian.Physical.Fermion

theorem entropy_ofClassical {d : Type*} [Fintype d] [DecidableEq d]
    (p : ProbDistribution d) : Sᵥₙ (MState.ofClassical p) = Hₛ p := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, MState.coe_ofClassical, HermitianMat.cfc_diagonal,
    HermitianMat.trace_diagonal]
  rfl

theorem negMulLog_mul (x y : ℝ) :
    Real.negMulLog (x*y) = y * Real.negMulLog x + x * Real.negMulLog y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.negMulLog, Real.log_mul hx hy, Real.negMulLog, Real.negMulLog]
  ring

theorem entropy_prod {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : MState d) (σ : MState e) : Sᵥₙ (ρ.prod σ) = Sᵥₙ ρ + Sᵥₙ σ := by
  obtain ⟨p,hp⟩ := MState.spectrum_prod ρ σ
  unfold Sᵥₙ Hₛ
  rw [← p.sum_comp (fun z => H₁ ((ρ.prod σ).spectrum.prob z)), Fintype.sum_prod_type]
  simp only [ProbDistribution.prob, hp, H₁, Prob.coe_mul]
  simp_rw [negMulLog_mul]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ProbDistribution.normalized, one_mul, mul_one]

def oneThermal (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) : MState Bool :=
  MState.ofClassical (ProbDistribution.mk'
    (fun b => if b then (1-t)/2 else (1+t)/2)
    (by intro b; cases b <;> simp <;> linarith [ht.1,ht.2])
    (by simp; ring))

theorem oneThermal_matrix (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (oneThermal t ht).m = Matrix.diagonal
      (fun b => ((if b then (1-t)/2 else (1+t)/2 : ℝ) : ℂ)) := rfl

theorem entropy_oneThermal (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Sᵥₙ (oneThermal t ht) = Gaussian.Entropy.fermion t := by
  rw [oneThermal, entropy_ofClassical]
  change (∑ b : Bool, Real.negMulLog (if b then (1-t)/2 else (1+t)/2)) = _
  rw [Fintype.sum_bool]
  exact add_comm _ _

def thermal : (n : ℕ) → (t : Fin n → ℝ) → (∀ i, t i ∈ Set.Icc (-1:ℝ) 1) → Density n
  | 0, _, _ => MState.ofClassical (ProbDistribution.constant ())
  | n+1, t, ht => (oneThermal (t 0) (ht 0)).prod
      (thermal n (fun i => t i.succ) (fun i => ht i.succ))

theorem entropy_thermal (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) :
    Sᵥₙ (thermal n t ht) = ∑ i, Gaussian.Entropy.fermion (t i) := by
  induction n with
  | zero => simp [thermal, entropy_ofClassical, Hₛ_constant_eq_zero]
  | succ n ih =>
    rw [thermal, entropy_prod, entropy_oneThermal, ih, Fin.sum_univ_succ]

theorem prod_expectation {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : MState d) (σ : MState e) (A : Matrix d d ℂ) (B : Matrix e e ℂ) :
    ((ρ.prod σ).m * (A ⊗ₖ B)).trace = (ρ.m * A).trace * (σ.m * B).trace := by
  change ((ρ.m ⊗ₖ σ.m) * (A ⊗ₖ B)).trace = _
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

@[simp] theorem oneThermal_parity (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    oneParity * (oneThermal t ht).m * oneParity = (oneThermal t ht).m := by
  rw [oneThermal_matrix]
  ext a b
  cases a <;> cases b <;> simp [oneParity, Matrix.mul_apply]

theorem thermal_parityInvariant (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) : ParityInvariant (thermal n t ht) := by
  unfold ParityInvariant
  induction n with
  | zero => simp [parity]
  | succ n ih =>
    change (oneParity ⊗ₖ parity n) *
      ((oneThermal (t 0) (ht 0)).m ⊗ₖ (thermal n (fun i => t i.succ) _).m) *
      (oneParity ⊗ₖ parity n) = _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, oneThermal_parity, ih]
    rfl

theorem oneThermal_majorana_pair (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (a b : Bool) :
    ((oneThermal t ht).m * (oneMajorana a * oneMajorana b)).trace =
      if a=b then (1 : ℂ) else if a then -Complex.I * t else Complex.I * t := by
  rw [oneThermal_matrix]
  cases a <;> cases b <;> simp [oneMajorana, Matrix.mul_apply, Matrix.trace] <;> ring

theorem oneThermal_majorana_parity (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (a : Bool) :
    ((oneThermal t ht).m * (oneMajorana a * oneParity)).trace = 0 := by
  rw [oneThermal_matrix]
  cases a <;> simp [oneMajorana, oneParity, Matrix.mul_apply, Matrix.trace]

theorem oneThermal_parity_majorana (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (a : Bool) :
    ((oneThermal t ht).m * (oneParity * oneMajorana a)).trace = 0 := by
  rw [(neg_eq_iff_eq_neg.mpr (oneMajorana_parity a)).symm, Matrix.mul_neg,
    Matrix.trace_neg, oneThermal_majorana_parity, neg_zero]

theorem thermal_twoPoint (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i j : Fin n) (a b : Bool) :
    moment (thermal n t ht) [(i,a),(j,b)] =
      if i=j then (if a=b then (1 : ℂ) else if a then -Complex.I * t i else Complex.I * t i)
      else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [moment_pair, majorana_zero, majorana_zero, thermal,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, prod_expectation]
      simp only [Matrix.mul_one, MState.tr', mul_one, oneThermal_majorana_pair, ite_true]
    · rw [moment_pair, majorana_zero, majorana_succ, thermal,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, prod_expectation,
        oneThermal_majorana_parity, zero_mul]
      simp [Ne.symm (Fin.succ_ne_zero j)]
    · rw [moment_pair, majorana_succ, majorana_zero, thermal,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one, prod_expectation,
        oneThermal_parity_majorana, zero_mul]
      simp
    · rw [moment_pair, majorana_succ, majorana_succ, thermal,
        ← Matrix.mul_kronecker_mul, oneParity_square, prod_expectation]
      rw [Matrix.mul_one, MState.tr', one_mul, ← moment_pair, ih]
      simp only [Fin.succ_inj]

theorem thermal_covariance (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i j : Fin n) (a b : Bool) :
    covariance (thermal n t ht) (i,a) (j,b) =
      if i=j then (if a=b then 0 else if a then -t i else t i) else 0 := by
  rw [covariance_eq_im_twoPoint, thermal_twoPoint]
  split_ifs <;> simp [Complex.mul_im]

end Gaussian.Physical.Fermion
