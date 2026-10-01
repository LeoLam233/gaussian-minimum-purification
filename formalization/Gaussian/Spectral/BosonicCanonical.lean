import Gaussian.Spectral.BosonicSimilarity
import Gaussian.Spectral.PairEigenbasis
import Gaussian.Spectral.Complexification

/-! Independent Hermitian two-form spectrum in canonical real mode coordinates. -/
noncomputable section
open Module
open scoped Matrix BigOperators ComplexOrder
namespace Gaussian.Spectral

def canonicalModeSkew (n : ℕ) : Matrix (Fin n × Bool) (Fin n × Bool) ℝ :=
  fun i j => if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1) else (if j.2 then 1 else 0)) else 0

def canonicalModeHermitian (n : ℕ) : Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  Complex.I • complexifyMatrix (canonicalModeSkew n)

def pairedDiagonal (n : ℕ) (ν : Fin n → ℝ) : Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  Matrix.diagonal (fun i => (ν i.1 : ℂ))

theorem canonicalModeHermitian_sq (n : ℕ) :
    canonicalModeHermitian n * canonicalModeHermitian n = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  cases a <;> cases b <;> simp [canonicalModeHermitian, complexifyMatrix, canonicalModeSkew,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite, mul_ite, ite_mul,
    Finset.sum_ite_eq', Complex.I_sq]

theorem canonicalModeHermitian_inv (n : ℕ) :
    (canonicalModeHermitian n)⁻¹ = canonicalModeHermitian n :=
  Matrix.inv_eq_left_inv (canonicalModeHermitian_sq n)

theorem bosonCanonical_mulVec (n : ℕ) (ν : Fin n → ℝ) (z : (Fin n × Bool) → ℂ)
    (i : Fin n) (a : Bool) :
    ((-(canonicalModeHermitian n)⁻¹ * pairedDiagonal n ν) *ᵥ z) (i,a) =
      if a then Complex.I * (ν i : ℂ) * z (i,false) else -Complex.I * (ν i : ℂ) * z (i,true) := by
  rw [canonicalModeHermitian_inv]
  cases a <;> simp [canonicalModeHermitian, complexifyMatrix, canonicalModeSkew,
    pairedDiagonal, Matrix.mul_diagonal, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul, Finset.sum_ite_eq']

theorem bosonCanonical_pair_eigen (n : ℕ) (ν : Fin n → ℝ) (i : Fin n) (a : Bool) :
    (-(canonicalModeHermitian n)⁻¹ * pairedDiagonal n ν) *ᵥ pairEigenbasis n (i,a) =
      ((if a then ν i else -ν i : ℝ) : ℂ) • pairEigenbasis n (i,a) := by
  ext ⟨j,b⟩
  rw [bosonCanonical_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, pairEigenbasis_apply]
  cases a <;> cases b <;> by_cases h : i=j <;> simp [h, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]

/-- The independent bosonic Hermitian-pair objective is the once-per-mode
Williamson entropy sum whenever BOTH original forms have the displayed canonical
coefficients. The basis is not presumed Euclidean-orthogonal. -/
theorem bosonPairCost_eq_sum_canonical {n : ℕ}
    (V O : HermitianMat (Fin n × Bool) ℂ) (hV : V.mat.PosDef)
    (B : Matrix (Fin n × Bool) (Fin n × Bool) ℂ) (hB : IsUnit B.det)
    (ν : Fin n → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (hO : B.conjTranspose * O.mat * B = canonicalModeHermitian n)
    (hD : B.conjTranspose * V.mat * B = pairedDiagonal n ν) :
    Gaussian.Attainment.bosonPairCost V O = ∑ i, Gaussian.Entropy.boson (ν i) := by
  have he (i : Fin n × Bool) :
      (-(B.conjTranspose * O.mat * B)⁻¹ * (B.conjTranspose * V.mat * B)) *ᵥ pairEigenbasis n i =
        ((if i.2 then ν i.1 else -ν i.1 : ℝ) : ℂ) • pairEigenbasis n i := by
    rw [hO,hD]
    exact bosonCanonical_pair_eigen n ν i.1 i.2
  rw [Gaussian.Attainment.bosonPairCost, Gaussian.Attainment.bosonHermitianCost,
    bosonPair_trace_eq_generalized_eigenbasis V O hV B hB (pairEigenbasis n)
      (fun i => if i.2 then ν i.1 else -ν i.1) he]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    abs_neg, abs_of_nonneg (hν _), Finset.sum_add_distrib]
  ring

end Gaussian.Spectral
