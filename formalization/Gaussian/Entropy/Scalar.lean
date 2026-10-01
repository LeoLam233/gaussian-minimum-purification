import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! The scalar entropy functions, continuously extended at the pure endpoint.
These scalar formulas are not definitions of entropy of a physical Gaussian state. -/
noncomputable section
namespace Gaussian.Entropy

def fermion (x : ℝ) : ℝ :=
  Real.negMulLog ((1+x)/2) + Real.negMulLog ((1-x)/2)
def boson (x : ℝ) : ℝ :=
  Real.negMulLog ((x-1)/2) - Real.negMulLog ((x+1)/2)

theorem continuous_fermion : Continuous fermion := by unfold fermion; fun_prop
theorem continuous_boson : Continuous boson := by unfold boson; fun_prop
@[simp] theorem fermion_one : fermion 1 = 0 := by norm_num [fermion]
@[simp] theorem boson_one : boson 1 = 0 := by norm_num [boson]

/-- Differentiation is only used away from the endpoints; continuity treats them. -/
theorem hasDerivAt_fermion {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    HasDerivAt fermion ((Real.log ((1-x)/2) - Real.log ((1+x)/2))/2) x := by
  have hp : (1+x)/2 ≠ 0 := by linarith [hx.1]
  have hq : (1-x)/2 ≠ 0 := by linarith [hx.2]
  have ha := (Real.hasDerivAt_negMulLog hp).comp x (((hasDerivAt_id x).const_add 1).div_const 2)
  have hb := (Real.hasDerivAt_negMulLog hq).comp x (((hasDerivAt_id x).const_sub 1).div_const 2)
  convert ha.add hb using 1
  · rfl
  · ring

theorem hasDerivAt_boson {x : ℝ} (hx : 1 < x) :
    HasDerivAt boson ((Real.log ((x+1)/2) - Real.log ((x-1)/2))/2) x := by
  have hp : (x+1)/2 ≠ 0 := by linarith
  have hq : (x-1)/2 ≠ 0 := by linarith
  have ha := (Real.hasDerivAt_negMulLog hq).comp x (((hasDerivAt_id x).sub_const 1).div_const 2)
  have hb := (Real.hasDerivAt_negMulLog hp).comp x (((hasDerivAt_id x).add_const 1).div_const 2)
  convert ha.sub hb using 1
  · rfl
  · ring

/-- Strict entropy decrease, including the pure endpoint x=1 and zero mode x=0. -/
theorem strictAntiOn_fermion : StrictAntiOn fermion (Set.Icc (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_fermion.continuousOn
  intro x hx
  have hx' : 0 < x ∧ x < 1 := by simpa only [interior_Icc, Set.mem_Ioo] using hx
  rw [(hasDerivAt_fermion (show x ∈ Set.Ioo (-1:ℝ) 1 by constructor <;> linarith)).deriv]
  have hl := Real.log_lt_log (show 0 < (1-x)/2 by linarith) (show (1-x)/2 < (1+x)/2 by linarith)
  linarith

theorem strictMonoOn_boson : StrictMonoOn boson (Set.Ici (1:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) continuous_boson.continuousOn
  intro x hx
  have hx' : 1 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  rw [(hasDerivAt_boson hx').deriv]
  have hl := Real.log_lt_log (show 0 < (x-1)/2 by linarith) (show (x-1)/2 < (x+1)/2 by linarith)
  linarith

theorem fermion_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ fermion x := by
  simpa using strictAntiOn_fermion.antitoneOn hx (show (1:ℝ) ∈ Set.Icc 0 1 by simp) hx.2

theorem boson_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ boson x := by
  simpa using strictMonoOn_boson.monotoneOn (show (1:ℝ) ∈ Set.Ici 1 by simp) hx hx

theorem fermion_eq_zero_iff {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    fermion x = 0 ↔ x = 1 := by
  constructor
  · intro h
    apply strictAntiOn_fermion.injOn hx (show (1:ℝ) ∈ Set.Icc 0 1 by simp)
    simpa using h
  · rintro rfl; exact fermion_one

theorem boson_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : boson x = 0 ↔ x = 1 := by
  constructor
  · intro h
    apply strictMonoOn_boson.injOn hx (show (1:ℝ) ∈ Set.Ici 1 by simp)
    simpa using h
  · rintro rfl; exact boson_one

/-- An entropy sublevel bounds every finite bosonic parameter; there is no
fixed squeezing cutoff in this theorem. -/
theorem log_half_le_boson {x : ℝ} (hx : 1 ≤ x) :
    Real.log ((x+1)/2) ≤ boson x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; norm_num
  have hq : 0 < (x-1)/2 := by linarith
  have hpq : (x-1)/2 ≤ (x+1)/2 := by linarith
  have hl : Real.log ((x-1)/2) ≤ Real.log ((x+1)/2) :=
    Real.log_le_log hq hpq
  have hm := mul_nonneg (le_of_lt hq) (sub_nonneg.mpr hl)
  have he : boson x - Real.log ((x+1)/2) =
      ((x-1)/2) * (Real.log ((x+1)/2) - Real.log ((x-1)/2)) := by
    unfold boson Real.negMulLog
    ring
  linarith

theorem boson_parameter_bound {x C : ℝ} (hx : 1 ≤ x) (hC : boson x ≤ C) :
    x ≤ 2 * Real.exp C - 1 := by
  have h := (Real.log_le_iff_le_exp (show 0 < (x+1)/2 by linarith)).mp
    ((log_half_le_boson hx).trans hC)
  linarith

/-- The continuous scalar extension is bounded below on all nonnegative inputs.
This auxiliary fact is used only for matrix-functional coercivity, not to assert
that nonphysical parameters represent Gaussian states. -/
theorem exists_boson_lower_bound : ∃ β : ℝ, 0 ≤ β ∧ ∀ x : ℝ, 0 ≤ x → -β ≤ boson x := by
  obtain ⟨a,ha,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by simp⟩) continuous_boson.continuousOn
  refine ⟨max 0 (-boson a),le_max_left _ _,?_⟩
  intro x hx
  by_cases hx1 : 1 ≤ x
  · have h := boson_nonneg hx1
    have hm := le_max_left (0:ℝ) (-boson a)
    linarith
  · have h : boson a ≤ boson x := hmin (show x ∈ Set.Icc (0:ℝ) 1 from ⟨hx,le_of_lt (lt_of_not_ge hx1)⟩)
    have hm := le_max_right (0:ℝ) (-boson a)
    linarith

theorem boson_parameter_bound_nonnegative {x C : ℝ} (_hx : 0 ≤ x) (hC : boson x ≤ C) :
    x ≤ max 1 (2 * Real.exp C - 1) := by
  by_cases hx1 : 1 ≤ x
  · exact (boson_parameter_bound hx1 hC).trans (le_max_right _ _)
  · exact (le_of_lt (lt_of_not_ge hx1)).trans (le_max_left _ _)
end Gaussian.Entropy
