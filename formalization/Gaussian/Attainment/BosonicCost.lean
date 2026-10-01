import Gaussian.Attainment.FermionicCuts
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-! A spectral objective of an independently supplied covariance/form pair.
O is intended to be iΩ. Physical symplectic-spectrum identification is separate;
both restricted forms remain present in this definition. -/
noncomputable section
namespace Gaussian.Attainment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bosonHermitianCost (A : HermitianMat ι ℂ) : ℝ :=
  (A.cfc (fun x => Gaussian.Entropy.boson |x|)).trace / 2

theorem continuous_bosonHermitianCost : Continuous (bosonHermitianCost (ι := ι)) := by
  unfold bosonHermitianCost
  have hf : Continuous (fun x : ℝ => Gaussian.Entropy.boson |x|) :=
    Gaussian.Entropy.continuous_boson.comp continuous_abs
  exact (HermitianMat.trace_Continuous.comp (HermitianMat.cfc_continuous hf)).div_const 2

theorem bosonHermitianCost_eq (A : HermitianMat ι ℂ) :
    bosonHermitianCost A = (∑ i, Gaussian.Entropy.boson |A.H.eigenvalues i|)/2 := by
  rw [bosonHermitianCost, HermitianMat.trace_cfc_eq]

theorem continuousOn_hermitian_inv :
    ContinuousOn (fun A : HermitianMat ι ℂ => A⁻¹) {A | A.mat.det ≠ 0} := by
  rw [HermitianMat.continuousOn_iff_coe]
  intro A hA
  have hi : ContinuousAt (fun M : Matrix ι ι ℂ => M⁻¹) A.mat :=
    continuousAt_matrix_inv A.mat (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA)
  exact (hi.comp HermitianMat.continuous_mat.continuousAt).continuousWithinAt

/-- H = i V^(1/2) Ω⁻¹ V^(1/2) = −V^(1/2) (iΩ)⁻¹ V^(1/2).
Inversion is only used on the proved nondegenerate locus by subsequent theorems. -/
def bosonPairHermitian (V O : HermitianMat ι ℂ) : HermitianMat ι ℂ :=
  (-O⁻¹).conj V.sqrt.mat

def bosonPairCost (V O : HermitianMat ι ℂ) : ℝ := bosonHermitianCost (bosonPairHermitian V O)

theorem continuousOn_bosonPairHermitian :
    ContinuousOn (fun p : HermitianMat ι ℂ × HermitianMat ι ℂ => bosonPairHermitian p.1 p.2)
      {p | p.2.mat.det ≠ 0} := by
  rw [HermitianMat.continuousOn_iff_coe]
  have hs : Continuous (fun p : HermitianMat ι ℂ × HermitianMat ι ℂ => p.1.sqrt.mat) :=
    HermitianMat.continuous_mat.comp ((HermitianMat.cfc_continuous Real.continuous_sqrt).comp continuous_fst)
  have hi : ContinuousOn (fun p : HermitianMat ι ℂ × HermitianMat ι ℂ => (p.2⁻¹).mat)
      {p | p.2.mat.det ≠ 0} :=
    HermitianMat.continuous_mat.comp_continuousOn (continuousOn_hermitian_inv.comp continuous_snd.continuousOn (fun _ h => h))
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set (HermitianMat ι ℂ × HermitianMat ι ℂ) := {p | p.2.mat.det ≠ 0}
  have hs' : Continuous (fun p : S => p.val.1.sqrt.mat) := hs.comp continuous_subtype_val
  have hi' : Continuous (fun p : S => (p.val.2⁻¹).mat) :=
    continuousOn_iff_continuous_domRestrict.mp hi
  change Continuous (fun p : S => p.val.1.sqrt.mat * -(p.val.2⁻¹).mat * p.val.1.sqrt.mat.conjTranspose)
  exact (hs'.matrix_mul hi'.neg).matrix_mul hs'.matrix_conjTranspose

theorem continuousOn_bosonPairCost :
    ContinuousOn (fun p : HermitianMat ι ℂ × HermitianMat ι ℂ => bosonPairCost p.1 p.2)
      {p | p.2.mat.det ≠ 0} :=
  continuous_bosonHermitianCost.comp_continuousOn continuousOn_bosonPairHermitian

/-- Every absolute spectral parameter is bounded on a finite entropy sublevel.
This bound uses no simplicity, gap, or global squeezing cutoff. -/
theorem bosonHermitianCost_parameter_bound (A : HermitianMat ι ℂ) {C : ℝ}
    (hphys : ∀ i, 1 ≤ |A.H.eigenvalues i|) (hC : bosonHermitianCost A ≤ C) (i : ι) :
    |A.H.eigenvalues i| ≤ 2 * Real.exp (2*C) - 1 := by
  have hi : Gaussian.Entropy.boson |A.H.eigenvalues i| ≤
      ∑ j, Gaussian.Entropy.boson |A.H.eigenvalues j| :=
    Finset.single_le_sum (fun j _ => Gaussian.Entropy.boson_nonneg (hphys j)) (Finset.mem_univ i)
  have hc : Gaussian.Entropy.boson |A.H.eigenvalues i| ≤ 2*C := by
    rw [bosonHermitianCost_eq] at hC
    linarith
  exact Gaussian.Entropy.boson_parameter_bound (hphys i) hc
end Gaussian.Attainment
