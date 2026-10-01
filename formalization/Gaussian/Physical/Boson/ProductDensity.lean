import Gaussian.Physical.Boson.LeftReduction
import Gaussian.Physical.Boson.VectorFamilyMatrix
import Gaussian.Analysis.ScalarProductSum

/-! Actual product normal densities on the concrete Schrödinger product space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory Gaussian.Analysis WithLp
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem jointVectorFamily_hasSum {ι κ : Type*} (v : ι → Schrodinger E) (w : κ → Schrodinger F)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) :
    HasSum (fun ij : ι×κ => ‖jointProduct (v ij.1) (w ij.2)‖^2) 1 := by
  simpa only [jointProduct_norm,mul_pow,one_mul] using
    hasSum_scalar_product (fun i => ‖v i‖^2) (fun j => ‖w j‖^2) 1 1 hv hw

def jointFamilyDensity {ι κ : Type*} (v : ι → Schrodinger E) (w : κ → Schrodinger F)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) :
    NormalDensity (Schrodinger (JointConfiguration E F)) :=
  normalVectorFamily (fun ij : ι×κ => jointProduct (v ij.1) (w ij.2))
    (jointVectorFamily_hasSum v w hv hw)

theorem jointFamilyDensity_characteristic {ι κ : Type*}
    (v : ι → Schrodinger E) (w : κ → Schrodinger F)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (q p : JointConfiguration E F) :
    NormalDensity.characteristic (E := JointConfiguration E F)
      (jointFamilyDensity (E := E) (F := F) v w hv hw) q p=
      NormalDensity.characteristic (E := E) (normalVectorFamily (H := Schrodinger E) v hv)
        (ofLp q).1 (ofLp p).1 *
      NormalDensity.characteristic (E := F) (normalVectorFamily (H := Schrodinger F) w hw)
        (ofLp q).2 (ofLp p).2 := by
  have h1 := normalVectorFamily_expect_hasSum (H := Schrodinger E) v hv
    (weylOperator (E := E) (ofLp q).1 (ofLp p).1)
  have h2 := normalVectorFamily_expect_hasSum (H := Schrodinger F) w hw
    (weylOperator (E := F) (ofLp q).2 (ofLp p).2)
  have ht := normalVectorFamily_expect_hasSum (H := Schrodinger (JointConfiguration E F))
    (fun ij : ι×κ => jointProduct (E := E) (F := F) (v ij.1) (w ij.2))
    (jointVectorFamily_hasSum v w hv hw) (weylOperator q p)
  have hp := hasSum_scalar_product
    (fun i => ⟪v i,(weylOperator (ofLp q).1 (ofLp p).1 : Schrodinger E →L[ℂ] Schrodinger E) (v i)⟫_ℂ)
    (fun j => ⟪w j,(weylOperator (ofLp q).2 (ofLp p).2 : Schrodinger F →L[ℂ] Schrodinger F) (w j)⟫_ℂ)
    _ _ h1 h2
  have he (ij : ι×κ) :
      ⟪jointProduct (v ij.1) (w ij.2),(weylOperator q p :
        Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F))
        (jointProduct (v ij.1) (w ij.2))⟫_ℂ=
      ⟪v ij.1,(weylOperator (ofLp q).1 (ofLp p).1 : Schrodinger E →L[ℂ] Schrodinger E) (v ij.1)⟫_ℂ*
      ⟪w ij.2,(weylOperator (ofLp q).2 (ofLp p).2 : Schrodinger F →L[ℂ] Schrodinger F) (w ij.2)⟫_ℂ := by
    simp only [weylOperator_apply,weyl_jointProduct,jointProduct_inner]
  have ht' := ht.congr_fun (fun ij => (he ij).symm)
  exact ht'.unique hp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
def NormalDensity.product (ρ : NormalDensity (Schrodinger E))
    (σ : NormalDensity (Schrodinger F)) : NormalDensity (Schrodinger (JointConfiguration E F)) :=
  jointFamilyDensity (fun i => (CFC.sqrt ρ.operator.1) (chosenHilbertBasis (Schrodinger E) i))
    (fun j => (CFC.sqrt σ.operator.1) (chosenHilbertBasis (Schrodinger F) j))
    (ρ.sqrt_vectors_hasSum _) (σ.sqrt_vectors_hasSum _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem NormalDensity.characteristic_product (ρ : NormalDensity (Schrodinger E))
    (σ : NormalDensity (Schrodinger F)) (q p : JointConfiguration E F) :
    (ρ.product σ).characteristic q p=
      ρ.characteristic (ofLp q).1 (ofLp p).1 * σ.characteristic (ofLp q).2 (ofLp p).2 := by
  have h := jointFamilyDensity_characteristic
    (fun i => (CFC.sqrt ρ.operator.1) (chosenHilbertBasis (Schrodinger E) i))
    (fun j => (CFC.sqrt σ.operator.1) (chosenHilbertBasis (Schrodinger F) j))
    (ρ.sqrt_vectors_hasSum _) (σ.sqrt_vectors_hasSum _) q p
  rw [← ρ.eq_normalVectorFamily_sqrt _,← σ.eq_normalVectorFamily_sqrt _] at h
  exact h

theorem NormalDensity.leftReduction_product (ρ : NormalDensity (Schrodinger E))
    (σ : NormalDensity (Schrodinger F)) : (ρ.product σ).leftReduction=ρ := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_product]
  simp [leftConfigEmbedding_apply,NormalDensity.characteristic_zero]

end Gaussian.Physical.Boson
