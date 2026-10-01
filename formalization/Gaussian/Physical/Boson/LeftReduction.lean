import Gaussian.Physical.Boson.ProductRestriction
import Gaussian.Physical.Boson.WeylImplementation
import Gaussian.Analysis.ChosenHilbertBasis

/-! Basis-independent actual left-factor reduction and local displacement.
The chosen bases serve only the convergent positive Kraus construction. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory Gaussian.Analysis WithLp
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def NormalDensity.leftReduction (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) :
    NormalDensity (Schrodinger E) :=
  reductionWithBasis (chosenHilbertBasis (Schrodinger E)) (chosenHilbertBasis (Schrodinger F))
    (chosenHilbertBasis (Schrodinger (JointConfiguration E F))) ρ

theorem NormalDensity.characteristic_leftReduction
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (q p : E) :
    ρ.leftReduction.characteristic q p=ρ.characteristic (leftConfigEmbedding q) (leftConfigEmbedding p) :=
  reductionWithBasis_characteristic _ _ _ ρ q p

theorem reductionWithBasis_eq_leftReduction {ι κ : Type*}
    {w : Set (Schrodinger (JointConfiguration E F))}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (d : HilbertBasis w ℂ (Schrodinger (JointConfiguration E F)))
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) :
    reductionWithBasis b c d ρ=ρ.leftReduction := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [reductionWithBasis_characteristic,NormalDensity.characteristic_leftReduction]

theorem IsGaussianWith.leftReduction
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V) :
    IsGaussianWith ρ.leftReduction (m.comp leftPhaseEmbedding)
      (V.compl₁₂ leftPhaseEmbedding leftPhaseEmbedding) :=
  reductionWithBasis_gaussian _ _ _ hρ

theorem NormalDensity.leftReduction_displace
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (a b : JointConfiguration E F) :
    (ρ.displace a b).leftReduction=ρ.leftReduction.displace (ofLp a).1 (ofLp b).1 := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_displace,
    NormalDensity.characteristic_displace,NormalDensity.characteristic_leftReduction]
  congr 2
  simp [leftConfigEmbedding_apply,WithLp.prod_inner_apply]

theorem NormalDensity.leftReduction_displace_entropy
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (a b : JointConfiguration E F) :
    ((ρ.displace a b).leftReduction).entropy=ρ.leftReduction.entropy := by
  rw [ρ.leftReduction_displace,NormalDensity.entropy_displace]

theorem NormalDensity.leftReduction_conjugate_of_fixes_physical
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F)))
    {R : (JointConfiguration E F×JointConfiguration E F) ≃ₗ[ℝ]
      (JointConfiguration E F×JointConfiguration E F)}
    {U : unitary (Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F))}
    (hU : WeylImplements R U) (hR : ∀ z : E×E, R (leftPhaseEmbedding z)=leftPhaseEmbedding z) :
    (ρ.conjugate U).leftReduction=ρ.leftReduction := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_leftReduction,NormalDensity.characteristic_leftReduction]
  have he := hU.characteristic ρ (leftPhaseEmbedding (q,p))
  rw [hR (q,p)] at he
  exact he

end Gaussian.Physical.Boson
