import Gaussian.Algebra.StarBlockFactorization
import Gaussian.Physical.Boson.SymplecticBlocks
import Gaussian.Physical.Boson.UpperShear
import Gaussian.Physical.Boson.ConfigurationSymplectic

/-! Actual implementation of the invertible-pivot symplectic factorization.
The separate symmetric-pivot theorem removes this intermediate invertibility premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_weyl_implementation_of_isUnit_A (R : (E×E) ≃ₗ[ℝ] (E×E))
    (hR : ∀ z w, weylSymplecticForm E (R z) (R w)=weylSymplecticForm E z w)
    (hA : IsUnit (phaseBlockA R.toLinearMap)) :
    ∃ U : unitary (Schrodinger E →L[ℂ] Schrodinger E), WeylImplements R U := by
  let A := phaseBlockA R.toLinearMap
  let B := phaseBlockB R.toLinearMap
  let C := phaseBlockC R.toLinearMap
  let D := phaseBlockD R.toLinearMap
  obtain ⟨u,hu⟩ := hA
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit u
  have he : e.toContinuousLinearMap=A := hu
  have he_apply (x : E) : e x=A x := congrArg (fun T : E →L[ℝ] E => T x) he
  let Ai := e.symm.toContinuousLinearMap
  have hAAi : A*Ai=1 := by
    rw [← he]
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hAiA : Ai*A=1 := by
    rw [← he]
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have hrel := phaseBlock_symplectic_relations R hR
  obtain ⟨hK,hN,hD⟩ := Gaussian.Algebra.star_block_schur
    (A := A) (B := B) (C := C) (D := D) (A' := Ai) hAAi hAiA hrel.1 hrel.2.1 hrel.2.2
  let K := C*Ai
  let N := Ai*B
  have hKself : IsSelfAdjoint K := by change star K=K; exact hK
  have hNself : IsSelfAdjoint N := by change star N=N; exact hN
  have hKsym : ∀ x y, ⟪K x,y⟫=⟪x,K y⟫ := hKself.isSymmetric
  have hNsym : ∀ x y, ⟪N x,y⟫=⟪x,N y⟫ := hNself.isSymmetric
  have hAN : A*N=B := by
    change A*(Ai*B)=B
    rw [← mul_assoc,hAAi,one_mul]
  have hKA : K*A=C := by
    change C*Ai*A=C
    rw [mul_assoc,hAiA,mul_one]
  have hAN_apply (x : E) : A (N x)=B x := congrArg (fun T : E →L[ℝ] E => T x) hAN
  have hKA_apply (x : E) : K (A x)=C x := congrArg (fun T : E →L[ℝ] E => T x) hKA
  have hfactor : R=((upperShear N).trans (configurationPhaseMap e)).trans (chirpShear K) := by
    apply LinearEquiv.ext
    intro z
    change R.toLinearMap z = _
    rw [phaseBlock_decomposition]
    apply Prod.ext
    · change A z.1+B z.2=e (z.1+N z.2)
      rw [he_apply,map_add,hAN_apply]
    · change C z.1+D z.2=e.symm.toContinuousLinearMap.adjoint z.2+K (e (z.1+N z.2))
      rw [he_apply,map_add,hAN_apply,map_add,hKA_apply,hD]
      change C z.1+(K (B z.2)+star Ai z.2)=star Ai z.2+(C z.1+K (B z.2))
      abel
  refine ⟨(upperShearOperator N*configurationOperator e)*chirpOperator K,?_⟩
  rw [hfactor]
  exact ((upperShear_implements N hNsym).trans (configuration_implements e)).trans
    (chirp_implements K hKsym)

end Gaussian.Physical.Boson
