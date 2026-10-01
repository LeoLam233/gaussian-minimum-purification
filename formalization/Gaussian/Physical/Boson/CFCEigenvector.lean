import Gaussian.Physical.Boson.NormalEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

noncomputable section
namespace Gaussian.Physical.Boson
open scoped ContinuousFunctionalCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfcHom_apply_eigenvector (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (μ : spectrum ℝ A) (v : H) (hv : A v = (μ.1 : ℂ) • v)
    (f : C(spectrum ℝ A, ℝ)) :
    (cfcHom hA f) v = (f μ : ℂ) • v := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    change (cfcHom hA (algebraMap ℝ C(spectrum ℝ A, ℝ) r)) v = _
    rw [AlgHomClass.commutes]
    rfl
  | id => simpa [cfcHom_id] using hv
  | star_id => simpa only [map_star, cfcHom_id, hA.star_eq, ContinuousMap.star_apply,
      star_trivial, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using hv
  | add f g hf hg => simp only [map_add, add_apply,
      ContinuousMap.add_apply, Complex.ofReal_add, add_smul, hf, hg]
  | mul f g hf hg =>
    simp only [map_mul, mul_apply_eq_comp, ContinuousMap.mul_apply,
      Complex.ofReal_mul]
    rw [hg, map_smul, hf, smul_smul, mul_comm]
  | frequently f hf =>
    have hc : IsClosed {g : C(spectrum ℝ A, ℝ) | (cfcHom hA g) v = (g μ : ℂ) • v} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact hc.mem_of_frequently_of_tendsto hf Filter.tendsto_id

theorem eigenvalue_mem_real_spectrum (A : H →L[ℂ] H) (μ : ℝ) (v : H)
    (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v) : μ ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hz : (u : H →L[ℂ] H) v = 0 := by
    rw [hu]
    change (μ : ℂ) • v - A v = 0
    rw [hAv, sub_self]
  have hi := congrArg (fun B : H →L[ℂ] H => B v) u.inv_val
  simp only [mul_apply_eq_comp, hz, map_zero, one_apply] at hi
  exact hv hi.symm

theorem cfc_apply_eigenvector (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (μ : ℝ) (v : H) (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f A) v = (f μ : ℂ) • v := by
  rw [cfc_apply f A hA hf.continuousOn]
  exact cfcHom_apply_eigenvector A hA ⟨μ, eigenvalue_mem_real_spectrum A μ v hv hAv⟩ v hAv _

end Gaussian.Physical.Boson
