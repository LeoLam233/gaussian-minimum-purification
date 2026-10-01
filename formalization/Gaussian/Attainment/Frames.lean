import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

/-! Compactness of actual orthonormal frames, including the empty frame.
No quotient topology or unproved Grassmannian compactness is assumed. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Gaussian.Attainment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frameSet : Set (ι → E) := {v | Orthonormal ℝ v}

theorem frameSet_closed : IsClosed (frameSet (ι := ι) (E := E)) := by
  have he : frameSet (ι := ι) (E := E) =
      ⋂ i : ι, ⋂ j : ι, {v : ι → E | ⟪v i,v j⟫ = if i=j then 1 else 0} := by
    ext v
    simp only [frameSet, Set.mem_setOf_eq, Set.mem_iInter, orthonormal_iff_ite]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const

theorem frameSet_subset_closedBall : frameSet (ι := ι) (E := E) ⊆ Metric.closedBall 0 1 := by
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  exact le_of_eq (hv.norm_eq_one i)

theorem frameSet_compact [FiniteDimensional ℝ E] :
    IsCompact (frameSet (ι := ι) (E := E)) :=
  (isCompact_closedBall (0 : ι → E) 1).of_isClosed_subset frameSet_closed frameSet_subset_closedBall

/-- Every continuous objective on a nonempty frame space has an actual minimizer. -/
theorem exists_minimum_on_frames [FiniteDimensional ℝ E]
    (hne : (frameSet (ι := ι) (E := E)).Nonempty) (f : (ι → E) → ℝ)
    (hf : ContinuousOn f frameSet) :
    ∃ v ∈ frameSet (ι := ι) (E := E), ∀ w ∈ frameSet, f v ≤ f w :=
  frameSet_compact.exists_isMinOn hne hf
end Gaussian.Attainment
