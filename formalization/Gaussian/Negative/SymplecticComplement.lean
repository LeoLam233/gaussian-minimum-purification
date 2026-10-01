import Gaussian.Phase.CompatibleGeometry

/-! N3: the Euclidean complement of an actual symplectic coefficient plane need
not be the commuting subsystem complement. Both forms must be retained. -/
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace Gaussian.Negative

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
def e4 (i : Fin 4) : FourSpace := EuclideanSpace.single i 1

def canonicalOmega4 (x y : FourSpace) : ℝ :=
  x 0*y 1-x 1*y 0+x 2*y 3-x 3*y 2

/-- The displayed plane is symplectic (Ω(x,y)=1), but its displayed Euclidean
orthogonal vector fails to commute with x. -/
theorem euclidean_complement_is_not_symplectic_complement :
    let x : FourSpace := e4 0
    let y : FourSpace := e4 1+e4 2
    let u : FourSpace := e4 2-e4 1
    ⟪x,u⟫=0 ∧ ⟪y,u⟫=0 ∧ canonicalOmega4 x y=1 ∧ canonicalOmega4 x u = -1 := by
  dsimp
  constructor
  · simp [e4,inner_sub_right,EuclideanSpace.inner_single_left]
  constructor
  · simp [e4,inner_add_left,inner_sub_right,EuclideanSpace.inner_single_left]
  constructor <;> norm_num [canonicalOmega4,e4,PiLp.add_apply,PiLp.sub_apply,PiLp.single_apply]

end Gaussian.Negative
