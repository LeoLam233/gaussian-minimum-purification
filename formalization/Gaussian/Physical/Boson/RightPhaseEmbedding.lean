import Gaussian.Physical.Boson.ProductRestriction

/-! The exact right-factor embedding of the physical CCR phase space. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def rightConfigEmbedding : F →ₗ[ℝ] JointConfiguration E F :=
  (WithLp.linearEquiv 2 ℝ (E×F)).symm.toLinearMap.comp (LinearMap.inr ℝ E F)

def rightPhaseEmbedding : (F×F) →ₗ[ℝ] (JointConfiguration E F×JointConfiguration E F) :=
  (rightConfigEmbedding (E := E) (F := F)).prodMap rightConfigEmbedding

@[simp] theorem rightConfigEmbedding_apply (q : F) :
    rightConfigEmbedding (E := E) q=toLp 2 (0,q) := rfl

@[simp] theorem rightPhaseEmbedding_apply (z : F×F) :
    rightPhaseEmbedding (E := E) z=(rightConfigEmbedding z.1,rightConfigEmbedding z.2) := rfl

end Gaussian.Physical.Boson
