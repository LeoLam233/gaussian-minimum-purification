import Gaussian.Physical.Boson.ProductParseval
import Gaussian.Physical.Boson.VectorFamilyExpectation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Genuine positive trace-class reduction via the actual product-basis Kraus
vectors. Gaussianity and the covariance restriction formula are not fields. -/
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

theorem reducedVectorFamily_hasSum {ι κ δ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (v : δ → Schrodinger (JointConfiguration E F)) (hv : HasSum (fun i => ‖v i‖^2) 1) :
    HasSum (fun ij : δ×κ => ‖jointExtraction (c ij.2) (v ij.1)‖^2) 1 := by
  have hi (i : δ) := hasSum_jointExtraction_norm_sq b c (v i)
  have hs : Summable (fun ij : δ×κ => ‖jointExtraction (c ij.2) (v ij.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun i => (hi i).summable,hv.summable.congr (fun i => (hi i).tsum_eq.symm)⟩
  have he := (hs.hasSum.prod_fiberwise hi).unique hv
  simpa only [he] using hs.hasSum

def reducedFamilyDensity {ι κ δ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (v : δ → Schrodinger (JointConfiguration E F)) (hv : HasSum (fun i => ‖v i‖^2) 1) :
    NormalDensity (Schrodinger E) :=
  normalVectorFamily (fun ij : δ×κ => jointExtraction (c ij.2) (v ij.1))
    (reducedVectorFamily_hasSum b c v hv)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
def reductionWithBasis {ι κ : Type*} {w : Set (Schrodinger (JointConfiguration E F))}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (d : HilbertBasis w ℂ (Schrodinger (JointConfiguration E F)))
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) : NormalDensity (Schrodinger E) :=
  reducedFamilyDensity (E := E) (F := F) b c
    (fun i : w => (CFC.sqrt ρ.operator.1) (d i)) (ρ.sqrt_vectors_hasSum d)

theorem reducedFamilyDensity_expect_hasSum {ι κ δ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (v : δ → Schrodinger (JointConfiguration E F)) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (A : Schrodinger E →L[ℂ] Schrodinger E) :
    HasSum (fun ij : δ×κ => ⟪jointExtraction (c ij.2) (v ij.1),
      A (jointExtraction (c ij.2) (v ij.1))⟫_ℂ) ((reducedFamilyDensity b c v hv).expect A) :=
  normalVectorFamily_expect_hasSum _ _ A

end Gaussian.Physical.Boson
