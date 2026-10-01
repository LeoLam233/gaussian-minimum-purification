import Gaussian.Physical.Boson.WeylSymplectic

/-! Actual configuration operator blocks of a real phase-space linear map.
The adjoint relations are derived from preservation of the genuine Weyl commutator form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def phaseBlockA (R : (E×E) →ₗ[ℝ] (E×E)) : E →L[ℝ] E :=
  ((LinearMap.fst ℝ E E).comp (R.comp (LinearMap.inl ℝ E E))).toContinuousLinearMap

def phaseBlockB (R : (E×E) →ₗ[ℝ] (E×E)) : E →L[ℝ] E :=
  ((LinearMap.fst ℝ E E).comp (R.comp (LinearMap.inr ℝ E E))).toContinuousLinearMap

def phaseBlockC (R : (E×E) →ₗ[ℝ] (E×E)) : E →L[ℝ] E :=
  ((LinearMap.snd ℝ E E).comp (R.comp (LinearMap.inl ℝ E E))).toContinuousLinearMap

def phaseBlockD (R : (E×E) →ₗ[ℝ] (E×E)) : E →L[ℝ] E :=
  ((LinearMap.snd ℝ E E).comp (R.comp (LinearMap.inr ℝ E E))).toContinuousLinearMap

@[simp] lemma phaseBlockA_apply (R : (E×E) →ₗ[ℝ] (E×E)) (x : E) :
    phaseBlockA R x=(R (x,0)).1 := rfl
@[simp] lemma phaseBlockB_apply (R : (E×E) →ₗ[ℝ] (E×E)) (x : E) :
    phaseBlockB R x=(R (0,x)).1 := rfl
@[simp] lemma phaseBlockC_apply (R : (E×E) →ₗ[ℝ] (E×E)) (x : E) :
    phaseBlockC R x=(R (x,0)).2 := rfl
@[simp] lemma phaseBlockD_apply (R : (E×E) →ₗ[ℝ] (E×E)) (x : E) :
    phaseBlockD R x=(R (0,x)).2 := rfl

lemma phaseBlock_decomposition (R : (E×E) →ₗ[ℝ] (E×E)) (z : E×E) :
    R z=(phaseBlockA R z.1+phaseBlockB R z.2,phaseBlockC R z.1+phaseBlockD R z.2) := by
  have he : z=(z.1,0)+(0,z.2) := by ext <;> simp
  calc
    R z = R (z.1,0)+R (0,z.2) := by rw [he,map_add]; simp
    _ = _ := rfl

lemma phaseBlock_joint_kernel (R : (E×E) ≃ₗ[ℝ] (E×E)) (x : E)
    (hA : phaseBlockA R.toLinearMap x=0) (hC : phaseBlockC R.toLinearMap x=0) : x=0 := by
  have h : R (x,0)=R 0 := by
    rw [map_zero]
    exact Prod.ext hA hC
  exact congrArg Prod.fst (R.injective h)

/-- All three operator identities needed by the exact symplectic Gauss factorization. -/
theorem phaseBlock_symplectic_relations (R : (E×E) ≃ₗ[ℝ] (E×E))
    (hR : ∀ z w, weylSymplecticForm E (R z) (R w)=weylSymplecticForm E z w) :
    star (phaseBlockA R.toLinearMap)*phaseBlockC R.toLinearMap =
        star (phaseBlockC R.toLinearMap)*phaseBlockA R.toLinearMap ∧
    star (phaseBlockB R.toLinearMap)*phaseBlockD R.toLinearMap =
        star (phaseBlockD R.toLinearMap)*phaseBlockB R.toLinearMap ∧
    star (phaseBlockA R.toLinearMap)*phaseBlockD R.toLinearMap -
        star (phaseBlockC R.toLinearMap)*phaseBlockB R.toLinearMap = 1 := by
  constructor
  · apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    simp only [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    have h := hR (x,0) (y,0)
    simp only [weylSymplecticForm_apply,inner_zero_left,inner_zero_right,sub_zero] at h
    exact sub_eq_zero.mp h
  constructor
  · apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    simp only [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    have h := hR (0,x) (0,y)
    simp only [weylSymplecticForm_apply,inner_zero_left,inner_zero_right,sub_zero] at h
    exact sub_eq_zero.mp h
  · apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    simp only [sub_apply,mul_apply_eq_comp,inner_sub_right,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    change ⟪(R (x,0)).1,(R (0,y)).2⟫ - ⟪(R (x,0)).2,(R (0,y)).1⟫ = ⟪x,y⟫
    have h := hR (x,0) (0,y)
    simpa only [weylSymplecticForm_apply,inner_zero_left,inner_zero_right,sub_zero] using h

end Gaussian.Physical.Boson
