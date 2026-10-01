import Gaussian.Physical.Boson.ProductCompleteness
import Gaussian.Analysis.HilbertBasisParseval

/-! Exact Hilbert-space Parseval identities for the actual product extraction maps. -/
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

def jointExtraction (g : Schrodinger F) :
    Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger E :=
  (jointProductEmbedding g).adjoint

theorem jointExtraction_inner (g : Schrodinger F) (f : Schrodinger E)
    (u : Schrodinger (JointConfiguration E F)) :
    ⟪f,jointExtraction g u⟫_ℂ=⟪jointProduct f g,u⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (jointProductEmbedding g) f u

theorem jointExtraction_jointProduct (g g' : Schrodinger F) (f : Schrodinger E) :
    jointExtraction g (jointProduct f g')=⟪g,g'⟫_ℂ • f := by
  apply ext_inner_left ℂ
  intro h
  rw [jointExtraction_inner,jointProduct_inner,inner_smul_right,mul_comm]

theorem hasSum_jointExtraction_norm_sq {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (u : Schrodinger (JointConfiguration E F)) :
    HasSum (fun j => ‖jointExtraction (c j) u‖^2) (‖u‖^2) := by
  have ht := Gaussian.Analysis.hasSum_hilbert_coeff_norm_sq (jointProductBasis b c) u
  have ht' : HasSum (fun ji : κ×ι => ‖⟪jointProduct (b ji.2) (c ji.1),u⟫_ℂ‖^2) (‖u‖^2) := by
    simpa only [Function.comp_def,Equiv.prodComm_apply,Prod.swap,jointProductBasis_apply] using
      (Equiv.prodComm κ ι).hasSum_iff.mpr ht
  apply ht'.prod_fiberwise
  intro j
  simpa only [jointExtraction_inner] using
    Gaussian.Analysis.hasSum_hilbert_coeff_norm_sq b (jointExtraction (c j) u)

theorem hasSum_jointExtraction_inner {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (u v : Schrodinger (JointConfiguration E F)) :
    HasSum (fun j => ⟪jointExtraction (c j) u,jointExtraction (c j) v⟫_ℂ) ⟪u,v⟫_ℂ := by
  have ht := (jointProductBasis b c).hasSum_inner_mul_inner u v
  have ht' : HasSum (fun ji : κ×ι =>
      ⟪u,jointProduct (b ji.2) (c ji.1)⟫_ℂ*⟪jointProduct (b ji.2) (c ji.1),v⟫_ℂ) ⟪u,v⟫_ℂ := by
    simpa only [Function.comp_def,Equiv.prodComm_apply,Prod.swap,jointProductBasis_apply] using
      (Equiv.prodComm κ ι).hasSum_iff.mpr ht
  apply ht'.prod_fiberwise
  intro j
  have hc (x : Schrodinger E) :
      ⟪jointExtraction (c j) u,x⟫_ℂ=⟪u,jointProduct x (c j)⟫_ℂ := by
    rw [← inner_conj_symm,jointExtraction_inner,inner_conj_symm]
  simpa only [hc,jointExtraction_inner] using
    b.hasSum_inner_mul_inner (jointExtraction (c j) u) (jointExtraction (c j) v)

end Gaussian.Physical.Boson
