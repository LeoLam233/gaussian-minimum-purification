import Gaussian.Physical.Boson.ProductRestriction
import Gaussian.Physical.Boson.RightPhaseEmbedding
import Gaussian.Phase.BosonicPurificationProduct

/-! Exact algebraic coordinates for the physical direct sum of two CCR phase spaces. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open WithLp
variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def phaseProductEquiv : (JointConfiguration E F×JointConfiguration E F) ≃ₗ[ℝ] ((E×E)×(F×F)) :=
  ((WithLp.linearEquiv 2 ℝ (E×F)).prodCongr (WithLp.linearEquiv 2 ℝ (E×F))).trans
    (LinearEquiv.prodProdProdComm ℝ E F E F)

@[simp] theorem phaseProductEquiv_apply (z : JointConfiguration E F×JointConfiguration E F) :
    phaseProductEquiv E F z=(((ofLp z.1).1,(ofLp z.2).1),((ofLp z.1).2,(ofLp z.2).2)) := rfl

@[simp] theorem phaseProductEquiv_symm_apply (z : (E×E)×(F×F)) :
    (phaseProductEquiv E F).symm z=(toLp 2 (z.1.1,z.2.1),toLp 2 (z.1.2,z.2.2)) := rfl

theorem phaseProductEquiv_weylForm (z w : JointConfiguration E F×JointConfiguration E F) :
    Gaussian.Phase.productForm (weylSymplecticForm E) (weylSymplecticForm F)
      (phaseProductEquiv E F z) (phaseProductEquiv E F w)=
      weylSymplecticForm (JointConfiguration E F) z w := by
  simp [Gaussian.Phase.productForm,weylSymplecticForm_apply,WithLp.prod_inner_apply]
  ring

@[simp] theorem phaseProductEquiv_left (z : E×E) :
    phaseProductEquiv E F (leftPhaseEmbedding z)=(z,0) := by
  ext <;> rfl

@[simp] theorem phaseProductEquiv_right (z : F×F) :
    phaseProductEquiv E F (rightPhaseEmbedding z)=(0,z) := by
  ext <;> rfl

end Gaussian.Physical.Boson
