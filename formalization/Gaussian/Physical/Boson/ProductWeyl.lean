import Gaussian.Physical.Boson.ProductConfiguration

/-! Actual joint Weyl operators act componentwise on actual L² product vectors. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem joint_weylPhase (q p z : JointConfiguration E F) :
    weylPhase q p z=weylPhase (ofLp q).1 (ofLp p).1 (ofLp z).1 +
      weylPhase (ofLp q).2 (ofLp p).2 (ofLp z).2 := by
  simp only [weylPhase,WithLp.prod_inner_apply]
  ring

theorem joint_phase (q p z : JointConfiguration E F) :
    phase (weylPhase q p) z=phase (weylPhase (ofLp q).1 (ofLp p).1) (ofLp z).1 *
      phase (weylPhase (ofLp q).2 (ofLp p).2) (ofLp z).2 := by
  unfold phase
  rw [joint_weylPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

theorem weyl_jointProduct (q p : JointConfiguration E F)
    (f : Schrodinger E) (g : Schrodinger F) :
    weyl q p (jointProduct f g)=
      jointProduct (weyl (ofLp q).1 (ofLp p).1 f) (weyl (ofLp q).2 (ofLp p).2 g) := by
  apply Lp.ext
  have hshift := (measurePreserving_add_right volume q).quasiMeasurePreserving.ae_eq_comp
    (jointProduct_ae f g)
  have ha := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := (volume : Measure F))).ae_eq_comp
    (weyl_ae (ofLp q).1 (ofLp p).1 f)
  have hb := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E)) (ν := (volume : Measure F))).ae_eq_comp
    (weyl_ae (ofLp q).2 (ofLp p).2 g)
  have ha' := (WithLp.volume_preserving_ofLp E F).quasiMeasurePreserving.ae_eq_comp ha
  have hb' := (WithLp.volume_preserving_ofLp E F).quasiMeasurePreserving.ae_eq_comp hb
  filter_upwards [weyl_ae q p (jointProduct f g),hshift,ha',hb',
    jointProduct_ae (weyl (ofLp q).1 (ofLp p).1 f) (weyl (ofLp q).2 (ofLp p).2 g)] with z h1 h2 h3 h4 h5
  change jointProduct f g (z+q)=f ((ofLp z).1+(ofLp q).1)*g ((ofLp z).2+(ofLp q).2) at h2
  simp only [Function.comp_apply] at h3 h4
  rw [h1,h2,h5,h3,h4,joint_phase]
  ring

end Gaussian.Physical.Boson
