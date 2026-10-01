import Gaussian.Physical.Boson.ProductRestriction
import Gaussian.Phase.BosonicPurificationSymplectic

/-! The literal left CCR subsystem as an actual nondegenerate symplectic range,
with its exact finite mode count and an explicit equivalence to the configuration phase. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def physicalPhaseSubspace : Submodule ℝ (JointConfiguration E F×JointConfiguration E F) :=
  (leftPhaseEmbedding (E := E) (F := F)).range

theorem leftPhaseEmbedding_injective : Function.Injective (leftPhaseEmbedding (E := E) (F := F)) :=
  symplectic_embedding_injective (weylSymplecticForm E) (weylSymplecticForm (JointConfiguration E F))
    weylSymplecticForm_nondegenerate leftPhaseEmbedding weylSymplecticForm_leftPhase

def physicalPhaseEquiv : (E×E) ≃ₗ[ℝ] physicalPhaseSubspace E F :=
  LinearEquiv.ofInjective leftPhaseEmbedding (leftPhaseEmbedding_injective E F)

@[simp] theorem physicalPhaseEquiv_coe (z : E×E) :
    (physicalPhaseEquiv E F z : JointConfiguration E F×JointConfiguration E F)=leftPhaseEmbedding z := rfl

theorem physicalPhaseSubspace_nondegenerate :
    ((weylSymplecticForm (JointConfiguration E F)).restrict (physicalPhaseSubspace E F)).Nondegenerate :=
  symplectic_range_nondegenerate (weylSymplecticForm E) (weylSymplecticForm (JointConfiguration E F))
    weylSymplecticForm_nondegenerate leftPhaseEmbedding weylSymplecticForm_leftPhase

theorem physicalPhaseSubspace_finrank : finrank ℝ (physicalPhaseSubspace E F)=2*finrank ℝ E := by
  rw [← (physicalPhaseEquiv E F).finrank_eq,Module.finrank_prod]
  omega

end Gaussian.Physical.Boson
