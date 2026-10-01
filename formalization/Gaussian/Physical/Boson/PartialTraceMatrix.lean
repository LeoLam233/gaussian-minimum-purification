import Gaussian.Physical.Boson.LeftReduction
import Gaussian.Physical.Boson.VectorFamilyMatrix

/-! The constructed marginal is the actual operator partial trace: its matrix
coefficients are the absolutely convergent sum over a complete environment basis. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem reductionWithBasis_matrix_hasSum {ι κ : Type*}
    {w : Set (Schrodinger (JointConfiguration E F))}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (d : HilbertBasis w ℂ (Schrodinger (JointConfiguration E F)))
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (x y : Schrodinger E) :
    HasSum (fun j => ⟪jointProduct x (c j),ρ.operator.1 (jointProduct y (c j))⟫_ℂ)
      ⟪x,(reductionWithBasis b c d ρ).operator.1 y⟫_ℂ := by
  let v : w → Schrodinger (JointConfiguration E F) := fun i => (CFC.sqrt ρ.operator.1) (d i)
  have hv := ρ.sqrt_vectors_hasSum d
  have hc (j : κ) (u : Schrodinger (JointConfiguration E F)) :
      ⟪jointExtraction (c j) u,y⟫_ℂ=⟪u,jointProduct y (c j)⟫_ℂ := by
    rw [← inner_conj_symm,jointExtraction_inner,inner_conj_symm]
  have ht := normalVectorFamily_matrix_hasSum
    (fun ij : w×κ => jointExtraction (c ij.2) (v ij.1))
    (reducedVectorFamily_hasSum b c v hv) x y
  have ht' : HasSum (fun ji : κ×w =>
      ⟪jointProduct x (c ji.1),v ji.2⟫_ℂ*⟪v ji.2,jointProduct y (c ji.1)⟫_ℂ)
      ⟪x,(reductionWithBasis b c d ρ).operator.1 y⟫_ℂ := by
    simpa only [Function.comp_def,Equiv.prodComm_apply,Prod.swap,jointExtraction_inner,hc,
      reductionWithBasis,reducedFamilyDensity,v] using
      (Equiv.prodComm κ w).hasSum_iff.mpr ht
  exact ht'.prod_fiberwise (fun j => ρ.sqrt_matrix_hasSum d (jointProduct x (c j))
    (jointProduct y (c j)))

theorem NormalDensity.leftReduction_matrix_hasSum {κ : Type*}
    (c : HilbertBasis κ ℂ (Schrodinger F))
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (x y : Schrodinger E) :
    HasSum (fun j => ⟪jointProduct x (c j),ρ.operator.1 (jointProduct y (c j))⟫_ℂ)
      ⟪x,ρ.leftReduction.operator.1 y⟫_ℂ := by
  have h := reductionWithBasis_matrix_hasSum
    (Gaussian.Analysis.chosenHilbertBasis (Schrodinger E)) c
    (Gaussian.Analysis.chosenHilbertBasis (Schrodinger (JointConfiguration E F))) ρ x y
  rwa [reductionWithBasis_eq_leftReduction] at h

end Gaussian.Physical.Boson
