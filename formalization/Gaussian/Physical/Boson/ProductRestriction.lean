import Gaussian.Physical.Boson.ProductReduction
import Gaussian.Physical.Boson.GaussianPredicate
import Gaussian.Physical.Boson.WeylSymplectic

/-! Actual reduced normal density and its physical Weyl restriction. The state
was constructed by positive trace-class Kraus vectors, not by covariance data. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory WithLp
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def leftConfigEmbedding : E →ₗ[ℝ] JointConfiguration E F :=
  (WithLp.linearEquiv 2 ℝ (E×F)).symm.toLinearMap.comp (LinearMap.inl ℝ E F)

def leftPhaseEmbedding : (E×E) →ₗ[ℝ] (JointConfiguration E F×JointConfiguration E F) :=
  (leftConfigEmbedding (E := E) (F := F)).prodMap leftConfigEmbedding

@[simp] theorem leftConfigEmbedding_apply (q : E) :
    leftConfigEmbedding (F := F) q=toLp 2 (q,0) := rfl

@[simp] theorem leftPhaseEmbedding_apply (z : E×E) :
    leftPhaseEmbedding (F := F) z=(leftConfigEmbedding z.1,leftConfigEmbedding z.2) := rfl

theorem weylSymplecticForm_leftPhase (z w : E×E) :
    weylSymplecticForm (JointConfiguration E F) (leftPhaseEmbedding z) (leftPhaseEmbedding w)=
      weylSymplecticForm E z w := by
  simp [weylSymplecticForm_apply,leftPhaseEmbedding_apply,leftConfigEmbedding_apply,
    WithLp.prod_inner_apply]

theorem weyl_left_jointProduct (q p : E) (f : Schrodinger E) (g : Schrodinger F) :
    weyl (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) (jointProduct f g)=jointProduct (weyl q p f) g := by
  rw [weyl_jointProduct]
  change jointProduct (weyl q p f) (weyl (0:F) 0 g)=_
  rw [weyl_zero_apply]

theorem star_weyl_left_jointProduct (q p : E) (f : Schrodinger E) (g : Schrodinger F) :
    star (weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) :
      Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F)) (jointProduct f g)=
      jointProduct (star (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) f) g := by
  simp only [weylOperator_star,weylOperator_apply]
  simpa only [map_neg] using weyl_left_jointProduct (-q) (-p) f g

theorem jointExtraction_left_weyl (q p : E) (g : Schrodinger F)
    (u : Schrodinger (JointConfiguration E F)) :
    jointExtraction g ((weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) :
      Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F)) u)=
      (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) (jointExtraction g u) := by
  apply ext_inner_left ℂ
  intro f
  rw [jointExtraction_inner]
  calc
    _ = ⟪star (weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) :
        Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F))
        (jointProduct f g),u⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪jointProduct (star (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) f) g,u⟫_ℂ := by
      rw [star_weyl_left_jointProduct]
    _ = ⟪star (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) f,jointExtraction g u⟫_ℂ :=
      (jointExtraction_inner _ _ _).symm
    _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]

theorem reducedFamilyDensity_characteristic {ι κ δ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (v : δ → Schrodinger (JointConfiguration E F)) (hv : HasSum (fun i => ‖v i‖^2) 1) (q p : E) :
    (reducedFamilyDensity b c v hv).characteristic q p=
      (normalVectorFamily v hv).characteristic (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) := by
  have hd := reducedFamilyDensity_expect_hasSum b c v hv (weylOperator q p)
  have hr (i : δ) : HasSum (fun j => ⟪jointExtraction (c j) (v i),
      (weylOperator q p : Schrodinger E →L[ℂ] Schrodinger E) (jointExtraction (c j) (v i))⟫_ℂ)
      ⟪v i,(weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) :
        Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F)) (v i)⟫_ℂ := by
    simpa only [jointExtraction_left_weyl] using hasSum_jointExtraction_inner b c (v i)
      ((weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) :
        Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger (JointConfiguration E F)) (v i))
  exact (hd.prod_fiberwise hr).unique (normalVectorFamily_expect_hasSum v hv
    (weylOperator (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem reductionWithBasis_characteristic {ι κ : Type*} {w : Set (Schrodinger (JointConfiguration E F))}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (d : HilbertBasis w ℂ (Schrodinger (JointConfiguration E F)))
    (ρ : NormalDensity (Schrodinger (JointConfiguration E F))) (q p : E) :
    (reductionWithBasis b c d ρ).characteristic q p=
      ρ.characteristic (leftConfigEmbedding (F := F) q) (leftConfigEmbedding (F := F) p) := by
  have h := reducedFamilyDensity_characteristic b c
    (fun i : w => (CFC.sqrt ρ.operator.1) (d i)) (ρ.sqrt_vectors_hasSum d) q p
  rw [← ρ.eq_normalVectorFamily_sqrt d] at h
  exact h

theorem reductionWithBasis_gaussian {ι κ : Type*} {w : Set (Schrodinger (JointConfiguration E F))}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (d : HilbertBasis w ℂ (Schrodinger (JointConfiguration E F)))
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V) :
    IsGaussianWith (reductionWithBasis b c d ρ) (m.comp leftPhaseEmbedding)
      (V.compl₁₂ leftPhaseEmbedding leftPhaseEmbedding) := by
  refine ⟨⟨fun x y => hρ.1.eq _ _⟩,?_⟩
  intro q p
  rw [reductionWithBasis_characteristic,hρ.2]
  rfl

end Gaussian.Physical.Boson
