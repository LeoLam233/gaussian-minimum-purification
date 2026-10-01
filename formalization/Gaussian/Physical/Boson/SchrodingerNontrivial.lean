import Gaussian.Physical.Boson.Weyl

/-! A genuine nonzero L² vector exists in every finite configuration dimension,
including dimension zero, by the finite positive-volume unit ball. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_nonzero_schrodinger : ∃ f : Schrodinger E, f≠0 := by
  let f : Schrodinger E := indicatorConstLp 2 (μ := (volume : Measure E))
    (s := Metric.ball (0:E) 1) measurableSet_ball measure_ball_lt_top.ne (1:ℂ)
  refine ⟨f,?_⟩
  intro he
  have hn := congrArg norm he
  change ‖indicatorConstLp 2 (μ := (volume : Measure E))
    (s := Metric.ball (0:E) 1) measurableSet_ball measure_ball_lt_top.ne (1:ℂ)‖=‖(0:Schrodinger E)‖ at hn
  rw [norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul,norm_zero] at hn
  have hp : 0<((volume : Measure E) (Metric.ball (0:E) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0:E) zero_lt_one).ne' measure_ball_lt_top.ne
  exact (Real.rpow_pos_of_pos hp _).ne' hn

theorem schrodinger_nontrivial : Nontrivial (Schrodinger E) := by
  obtain ⟨f,hf⟩ := exists_nonzero_schrodinger (E := E)
  exact nontrivial_of_ne f 0 hf

end Gaussian.Physical.Boson
