import Gaussian.Spectral.HermitianEigenbasis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Spectral
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def hermitianDirectSum (A : HermitianMat m ℂ) (B : HermitianMat n ℂ) : HermitianMat (m ⊕ n) ℂ :=
  ⟨Matrix.fromBlocks A.mat 0 0 B.mat, by
    change (Matrix.fromBlocks A.mat 0 0 B.mat).conjTranspose = _
    simp only [Matrix.fromBlocks_conjTranspose, HermitianMat.conjTranspose_mat,
      Matrix.conjTranspose_zero]⟩

theorem hermitianDirectSum_trace_cfc (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    (f : ℝ → ℝ) :
    ((hermitianDirectSum A B).cfc f).trace = (A.cfc f).trace + (B.cfc f).trace := by
  have hr : (hermitianDirectSum A B).mat.charpoly.roots = A.mat.charpoly.roots + B.mat.charpoly.roots := by
    change (Matrix.fromBlocks A.mat 0 0 B.mat).charpoly.roots = _
    rw [Matrix.charpoly_fromBlocks_zero₂₁, Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic A.mat).ne_zero (Matrix.charpoly_monic B.mat).ne_zero)]
  have h := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) hr
  rw [(hermitianDirectSum A B).H.roots_charpoly_eq_eigenvalues,
    A.H.roots_charpoly_eq_eigenvalues,B.H.roots_charpoly_eq_eigenvalues] at h
  simp only [Multiset.map_add,Multiset.sum_add,Multiset.map_map,Function.comp_def,
    ← Finset.sum_eq_multiset_sum] at h
  rw [HermitianMat.trace_cfc_eq,HermitianMat.trace_cfc_eq,HermitianMat.trace_cfc_eq]
  convert h using 1

end Gaussian.Spectral
