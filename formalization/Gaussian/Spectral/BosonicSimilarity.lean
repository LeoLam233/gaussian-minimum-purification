import Gaussian.Attainment.BosonicCost
import Gaussian.Spectral.HermitianEigenbasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Exact two-form congruence/similarity bridge for the independent bosonic
Hermitian matrix. No desired spectrum is used to define the physical matrix. -/
noncomputable section
open scoped Matrix ComplexOrder
open Module
namespace Gaussian.Spectral
variable {d : Type*} [Fintype d] [DecidableEq d]

lemma inverse_congruence (O B : Matrix d d ℂ) (hB : IsUnit B.det) :
    B * (B.conjTranspose * O * B)⁻¹ * B.conjTranspose = O⁻¹ := by
  have hBs : IsUnit B.conjTranspose.det := by simpa only [Matrix.det_conjTranspose] using hB.star
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    B * (B⁻¹ * (O⁻¹ * B.conjTranspose⁻¹)) * B.conjTranspose =
      (B*B⁻¹) * O⁻¹ * (B.conjTranspose⁻¹ * B.conjTranspose) := by simp only [mul_assoc]
    _ = O⁻¹ := by rw [Matrix.mul_nonsing_inv B hB,
      Matrix.nonsing_inv_mul B.conjTranspose hBs, one_mul, mul_one]

/-- The separately defined H intertwines with the generalized two-form operator
in every invertible coefficient frame; V and O are both transformed. -/
theorem bosonPair_intertwine (V O : HermitianMat d ℂ) (hV : 0 ≤ V)
    (B : Matrix d d ℂ) (hB : IsUnit B.det) :
    (Gaussian.Attainment.bosonPairHermitian V O).mat * (V.sqrt.mat * B) =
      (V.sqrt.mat * B) * (-(B.conjTranspose * O.mat * B)⁻¹ *
        (B.conjTranspose * V.mat * B)) := by
  have hInv := inverse_congruence O.mat B hB
  simp only [Gaussian.Attainment.bosonPairHermitian, HermitianMat.conj_apply_mat,
    HermitianMat.mat_neg, HermitianMat.mat_inv, HermitianMat.conjTranspose_mat]
  calc
    V.sqrt.mat * -O.mat⁻¹ * V.sqrt.mat * (V.sqrt.mat * B) =
      V.sqrt.mat * -O.mat⁻¹ * (V.sqrt.mat * V.sqrt.mat) * B := by simp only [mul_assoc]
    _ = V.sqrt.mat * -O.mat⁻¹ * V.mat * B := by rw [HermitianMat.sqrt_sq hV]
    _ = _ := by rw [← hInv]; simp only [mul_assoc, neg_mul, mul_neg]

/-- Similarity transports an arbitrary complete eigenbasis to the separately
constructed Hermitian bosonic matrix, retaining algebraic multiplicities. -/
theorem bosonPair_trace_eq_generalized_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V O : HermitianMat d ℂ) (hV : V.mat.PosDef)
    (B : Matrix d d ℂ) (hB : IsUnit B.det)
    (b : Basis ι ℂ (d → ℂ)) (a : ι → ℝ)
    (he : ∀ i, (-(B.conjTranspose * O.mat * B)⁻¹ * (B.conjTranspose * V.mat * B)) *ᵥ b i =
      (a i : ℂ) • b i) (f : ℝ → ℝ) :
    ((Gaussian.Attainment.bosonPairHermitian V O).cfc f).trace = ∑ i, f (a i) := by
  let S := V.sqrt.mat * B
  have hS : IsUnit S.det := by
    rw [Matrix.det_mul]
    exact (isUnit_iff_ne_zero.mpr (HermitianMat.sqrt_posDef hV).det_pos.ne').mul hB
  let e := Matrix.toLinearEquiv (Pi.basisFun ℂ d) S hS
  have heval (x : d → ℂ) : e x = S *ᵥ x := by
    simp only [e, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  apply hermitian_trace_cfc_eq_eigenbasis_sum _ (b.map e) a _ f
  intro i
  simp only [Basis.map_apply, heval]
  rw [Matrix.mulVec_mulVec, bosonPair_intertwine V O (HermitianMat.zero_le_iff.mpr hV.posSemidef) B hB,
    ← Matrix.mulVec_mulVec, he i, Matrix.mulVec_smul]

end Gaussian.Spectral
