import Gaussian.Physical.Boson.OperatorPivot
import Gaussian.Physical.Boson.InvertibleSymplectic

/-! Every finite real symplectic phase map has a concrete Schrödinger unitary implementation.
A proved symmetric pivot removes singular coordinate blocks. There is no global squeezing bound
and no implementation-existence field or axiom. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Constructive finite-generator implementation of every actual Weyl-symplectic linear equivalence. -/
theorem exists_weyl_implementation (R : (E×E) ≃ₗ[ℝ] (E×E))
    (hR : ∀ z w, weylSymplecticForm E (R z) (R w)=weylSymplecticForm E z w) :
    ∃ U : unitary (Schrodinger E →L[ℂ] Schrodinger E), WeylImplements R U := by
  obtain ⟨S,hS,hunit⟩ := exists_selfAdjoint_operator_pivot
    (phaseBlockA R.toLinearMap) (phaseBlockC R.toLinearMap)
    (phaseBlock_joint_kernel R) (phaseBlock_symplectic_relations R hR).1
  let R' := R.trans (upperShear S)
  have hR' : ∀ z w, weylSymplecticForm E (R' z) (R' w)=weylSymplecticForm E z w := by
    intro z w
    exact (upperShear_symplectic S hS.isSymmetric (R z) (R w)).trans (hR z w)
  have hA' : phaseBlockA R'.toLinearMap = phaseBlockA R.toLinearMap+S*phaseBlockC R.toLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  obtain ⟨U,hU⟩ := exists_weyl_implementation_of_isUnit_A R' hR' (hA'.symm ▸ hunit)
  have he : R'.trans (upperShear S).symm=R := by
    apply LinearEquiv.ext
    intro z
    exact (upperShear S).symm_apply_apply (R z)
  refine ⟨U*star (upperShearOperator S),?_⟩
  simpa only [he] using hU.trans (upperShear_implements S hS.isSymmetric).symm

end Gaussian.Physical.Boson
