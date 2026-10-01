import Gaussian.Physical.Boson.RightReduction

/-! Operator factorization of actual Gaussian densities from a proved vanishing
cross covariance, using genuine partial traces and Weyl density injectivity. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem jointPhase_decomposition (q p : JointConfiguration E F) :
    leftPhaseEmbedding ((ofLp q).1,(ofLp p).1)+
      rightPhaseEmbedding ((ofLp q).2,(ofLp p).2)=(q,p) := by
  apply Prod.ext <;> apply (WithLp.linearEquiv 2 ℝ (E×F)).injective <;>
    ext <;> simp [leftPhaseEmbedding_apply,rightPhaseEmbedding_apply,
      leftConfigEmbedding_apply,rightConfigEmbedding_apply]

theorem IsGaussianWith.characteristic_factors_of_cross_zero
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V)
    (hcross : ∀ z : E×E,∀ w : F×F,V (leftPhaseEmbedding z) (rightPhaseEmbedding w)=0)
    (q p : JointConfiguration E F) :
    ρ.characteristic q p=ρ.leftReduction.characteristic (ofLp q).1 (ofLp p).1 *
      ρ.rightReduction.characteristic (ofLp q).2 (ofLp p).2 := by
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_rightReduction,
    hρ.2,hρ.2,hρ.2,← Complex.exp_add]
  congr 1
  let z : E×E := ((ofLp q).1,(ofLp p).1)
  let w : F×F := ((ofLp q).2,(ofLp p).2)
  have hm : m (q,p)=m (leftPhaseEmbedding z)+m (rightPhaseEmbedding w) := by
    rw [← jointPhase_decomposition q p,map_add]
  have hv : V (q,p) (q,p)=V (leftPhaseEmbedding z) (leftPhaseEmbedding z)+
      V (rightPhaseEmbedding w) (rightPhaseEmbedding w) := by
    rw [← jointPhase_decomposition q p]
    simp only [map_add,LinearMap.add_apply]
    rw [hcross z w,hρ.1.eq (rightPhaseEmbedding w) (leftPhaseEmbedding z),hcross z w]
    ring
  change _=(_:_)+_
  rw [hm,hv]
  simp only [leftPhaseEmbedding_apply,rightPhaseEmbedding_apply,z,w]
  push_cast
  ring

theorem IsGaussianWith.eq_product_of_cross_zero
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V)
    (hcross : ∀ z : E×E,∀ w : F×F,V (leftPhaseEmbedding z) (rightPhaseEmbedding w)=0) :
    ρ=ρ.leftReduction.product ρ.rightReduction :=
  ρ.eq_product_of_characteristic_factors (hρ.characteristic_factors_of_cross_zero hcross)

end Gaussian.Physical.Boson
