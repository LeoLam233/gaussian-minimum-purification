import Gaussian.Physical.Fermion.StateAction

/-! Physical covariance admissibility is derived from density positivity and CAR,
not assumed as a field of a physical-state interface. -/
noncomputable section
open scoped Matrix BigOperators ComplexOrder
namespace Gaussian.Physical.Fermion

def twoPointMatrix {n : ℕ} (ρ : Density n) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ :=
  fun a b => moment ρ [a,b]

@[simp] theorem majoranaSum_adjoint (n : ℕ) (v : MajoranaIndex n → ℂ) :
    (majoranaSum n v)ᴴ = majoranaSum n (fun a => star (v a)) := by
  simp [majoranaSum, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]

theorem twoPointMatrix_quadratic {n : ℕ} (ρ : Density n) (v : MajoranaIndex n → ℂ) :
    star v ⬝ᵥ (twoPointMatrix ρ *ᵥ v) =
      (ρ.m * ((majoranaSum n v)ᴴ * majoranaSum n v)).trace := by
  rw [majoranaSum_adjoint]
  unfold majoranaSum twoPointMatrix
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mulVec, dotProduct,
    Pi.star_apply, moment_pair]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem twoPointMatrix_posSemidef {n : ℕ} (ρ : Density n) :
    (twoPointMatrix ρ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext a b
    exact twoPoint_star ρ b a
  · intro v
    rw [twoPointMatrix_quadratic]
    have h := (ρ.psd.mul_mul_conjTranspose_same (majoranaSum n v)).trace_nonneg
    rwa [Matrix.trace_mul_cycle, Matrix.trace_mul_comm] at h

def hermitianCovariance {n : ℕ} (ρ : Density n) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ :=
  fun a b => Complex.I * (covariance ρ a b : ℂ)

theorem twoPointMatrix_eq_one_add {n : ℕ} (ρ : Density n) :
    twoPointMatrix ρ = 1 + hermitianCovariance ρ := by
  ext a b
  exact twoPoint_eq_delta_add_covariance ρ a b

theorem one_add_hermitianCovariance_posSemidef {n : ℕ} (ρ : Density n) :
    (1 + hermitianCovariance ρ).PosSemidef := by
  rw [← twoPointMatrix_eq_one_add]
  exact twoPointMatrix_posSemidef ρ

theorem one_sub_hermitianCovariance_posSemidef {n : ℕ} (ρ : Density n) :
    (1 - hermitianCovariance ρ).PosSemidef := by
  have h := (twoPointMatrix_posSemidef ρ).transpose
  have he : (twoPointMatrix ρ)ᵀ = 1-hermitianCovariance ρ := by
    rw [twoPointMatrix_eq_one_add]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, hermitianCovariance]
    rw [covariance_skew ρ b a]
    simp [eq_comm, sub_eq_add_neg]
  rwa [he] at h

end Gaussian.Physical.Fermion
