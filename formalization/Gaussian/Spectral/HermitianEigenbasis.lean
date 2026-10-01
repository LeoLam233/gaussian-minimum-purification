import QuantumInfo.ForMathlib.HermitianMat.CFC
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! A trace-CFC formula from any actual complex eigenbasis. Orthogonality is
not assumed; multiplicities are matched through characteristic-polynomial roots. -/
noncomputable section
open Module
open scoped Matrix BigOperators
namespace Gaussian.Spectral

/-- Arbitrary complex eigenbases identify the trace of real functional calculus
on an independently Hermitian matrix, including repeated eigenvalues. -/
theorem hermitian_trace_cfc_eq_eigenbasis_sum {d ι : Type*}
    [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]
    (H : HermitianMat d ℂ) (b : Basis ι ℂ (d → ℂ)) (a : ι → ℝ)
    (he : ∀ i, H.mat *ᵥ b i = (a i : ℂ) • b i) (f : ℝ → ℝ) :
    (H.cfc f).trace = ∑ i, f (a i) := by
  let T := Matrix.toLin' H.mat
  have hm : T.toMatrix b b = Matrix.diagonal (fun i => (a i : ℂ)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply,T,Matrix.toLin'_apply,he,map_smul,
      Finsupp.smul_apply,smul_eq_mul,Matrix.diagonal_apply,Basis.repr_self,Finsupp.single_apply]
    split_ifs <;> simp_all
  have hr : H.mat.charpoly.roots = Multiset.map (fun i => (a i : ℂ)) Finset.univ.val := by
    rw [← Matrix.charpoly_toLin',← T.charpoly_toMatrix b,hm,Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero])]
    simp
  have hs := H.H.roots_charpoly_eq_eigenvalues
  have h := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) (hs.symm.trans hr)
  rw [HermitianMat.trace_cfc_eq]
  simp only [Multiset.map_map,Function.comp_def,← Finset.sum_eq_multiset_sum] at h
  convert h using 1

end Gaussian.Spectral
