import Gaussian.Attainment.Frames
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Linarith

/-! Nondegenerate-limit compactness expressed with a quantitative lower bound.
This avoids assuming continuity of a smallest singular value or bounded squeezing. -/
noncomputable section
namespace Gaussian.Attainment
variable {𝕜 X E : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def nondegenerateLocus (T : X → E →L[𝕜] E) : Set X := {p | Function.Injective (T p)}
def lowerBoundLocus (T : X → E →L[𝕜] E) (ε : ℝ) : Set X :=
  {p | ∀ x, ε * ‖x‖ ≤ ‖T p x‖}

theorem lowerBoundLocus_closed (T : X → E →L[𝕜] E) (hT : Continuous T) (ε : ℝ) :
    IsClosed (lowerBoundLocus T ε) := by
  have he : lowerBoundLocus T ε = ⋂ x : E, {p : X | ε * ‖x‖ ≤ ‖T p x‖} := by
    ext p; simp [lowerBoundLocus]
  rw [he]
  exact isClosed_iInter (fun x => isClosed_le continuous_const ((hT.clm_apply continuous_const).norm))

theorem lowerBoundLocus_nondegenerate (T : X → E →L[𝕜] E) {ε : ℝ} (hε : 0 < ε) :
    lowerBoundLocus T ε ⊆ nondegenerateLocus T := by
  intro p hp x y hxy
  apply sub_eq_zero.mp
  have h := hp (x-y)
  rw [map_sub,hxy,sub_self,norm_zero] at h
  have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact norm_eq_zero.mp hz

/-- Quantitative injectivity survives every limit, even if the admissible locus is open. -/
theorem injective_of_mem_closure_lowerBound (T : X → E →L[𝕜] E)
    (hT : Continuous T) {ε : ℝ} (hε : 0 < ε) {p : X}
    (hp : p ∈ closure (lowerBoundLocus T ε)) : Function.Injective (T p) := by
  rw [(lowerBoundLocus_closed T hT ε).closure_eq] at hp
  exact lowerBoundLocus_nondegenerate T hε hp

/-- A finite entropy sublevel inside a compact frame set yields an exact minimizer,
provided the actual objective and actual restricted form satisfy the displayed bounds.
This is a general topological lemma; its hypotheses must be proved for Gaussian cuts. -/
theorem exists_minimum_of_sublevel_lowerBound (F : Set X) (hF : IsCompact F)
    (T : X → E →L[𝕜] E) (hT : Continuous T) (f : X → ℝ)
    (hf : ContinuousOn f (F ∩ nondegenerateLocus T))
    (p₀ : X) (hp₀ : p₀ ∈ F ∩ nondegenerateLocus T)
    (ε : ℝ) (hε : 0 < ε)
    (hsub : ∀ p ∈ F ∩ nondegenerateLocus T, f p ≤ f p₀ → p ∈ lowerBoundLocus T ε) :
    ∃ p ∈ F ∩ nondegenerateLocus T,
      ∀ q ∈ F ∩ nondegenerateLocus T, f p ≤ f q := by
  let C := F ∩ lowerBoundLocus T ε
  have hC : IsCompact C := hF.inter_right (lowerBoundLocus_closed T hT ε)
  have hcsub : C ⊆ F ∩ nondegenerateLocus T := by
    intro p hp
    exact ⟨hp.1,lowerBoundLocus_nondegenerate T hε hp.2⟩
  have hzero : p₀ ∈ C := ⟨hp₀.1,hsub p₀ hp₀ le_rfl⟩
  obtain ⟨p,hp,hmin⟩ := hC.exists_isMinOn ⟨p₀,hzero⟩ (hf.mono hcsub)
  refine ⟨p,hcsub hp,?_⟩
  intro q hq
  by_cases hq0 : f q ≤ f p₀
  · exact hmin ⟨hq.1,hsub q hq hq0⟩
  · exact (hmin hzero).trans (le_of_lt (lt_of_not_ge hq0))

/-- A genuine inverse operator-norm estimate yields the quantitative form bound. -/
theorem lower_bound_of_inverse_norm (T : E ≃L[𝕜] E) {C : ℝ} (hC : 0 < C)
    (hInv : ‖(T.symm : E →L[𝕜] E)‖ ≤ C) (x : E) :
    C⁻¹ * ‖x‖ ≤ ‖T x‖ := by
  have h := (T.symm : E →L[𝕜] E).le_opNorm (T x)
  change ‖T.symm (T x)‖ ≤ ‖(T.symm : E →L[𝕜] E)‖ * ‖T x‖ at h
  rw [T.symm_apply_apply] at h
  have h' : ‖x‖ ≤ C * ‖T x‖ := h.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h')
end Gaussian.Attainment
