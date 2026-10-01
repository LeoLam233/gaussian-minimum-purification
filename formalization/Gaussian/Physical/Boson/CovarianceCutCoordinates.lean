import Gaussian.Physical.Boson.CovarianceProductCoordinates
import Gaussian.Physical.Boson.PhysicalPhaseSubspace
import Gaussian.Physical.Boson.SidewiseDomain
import Gaussian.Phase.BosonicPurificationCuts

/-! The actual AA′ configuration phase is equivalent to the physical-left and
auxiliary-left symplectic ranges, with both restricted forms and their cost preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase WithLp
variable (A B C D : Type*)
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

def sidewiseCutEquiv : (JointConfiguration A C×JointConfiguration A C) ≃ₗ[ℝ]
    (physicalPhaseSubspace A B×physicalPhaseSubspace C D) :=
  (phaseProductEquiv A C).trans ((physicalPhaseEquiv A B).prodCongr (physicalPhaseEquiv C D))

lemma sidewiseCutEquiv_embedding (z : JointConfiguration A C×JointConfiguration A C) :
    (phaseProductEquiv (JointConfiguration A B) (JointConfiguration C D)).symm
      (auxiliaryCutMap (physicalPhaseSubspace A B) (physicalPhaseSubspace C D)
        (sidewiseCutEquiv A B C D z))=sidewisePhaseEmbedding (B := B) (D := D) z := by
  rcases z with ⟨q,p⟩
  rfl

lemma sidewiseCutEquiv_weylForm (z w : JointConfiguration A C×JointConfiguration A C) :
    productForm ((weylSymplecticForm (JointConfiguration A B)).restrict (physicalPhaseSubspace A B))
      ((weylSymplecticForm (JointConfiguration C D)).restrict (physicalPhaseSubspace C D))
      (sidewiseCutEquiv A B C D z) (sidewiseCutEquiv A B C D w)=
        weylSymplecticForm (JointConfiguration A C) z w := by
  change weylSymplecticForm (JointConfiguration A B)
      (leftPhaseEmbedding (phaseProductEquiv A C z).1) (leftPhaseEmbedding (phaseProductEquiv A C w).1)+
    weylSymplecticForm (JointConfiguration C D)
      (leftPhaseEmbedding (phaseProductEquiv A C z).2) (leftPhaseEmbedding (phaseProductEquiv A C w).2)=_
  rw [weylSymplecticForm_leftPhase,weylSymplecticForm_leftPhase]
  exact phaseProductEquiv_weylForm A C z w

theorem pureCovariance_sidewise_cost
    (d : PureCompatibleCovariance (weylSymplecticForm (FourConfiguration A B C D))) :
    (pureCovarianceProductCoordinates d).auxiliaryCutCost (physicalPhaseSubspace A B) (physicalPhaseSubspace C D)=
      bosonFormCost (Module.finBasis ℝ (JointConfiguration A C×JointConfiguration A C))
        (d.form.compl₁₂ sidewisePhaseEmbedding sidewisePhaseEmbedding)
        (weylSymplecticForm (JointConfiguration A C))
        ⟨fun x y => d.symmetric.eq _ _⟩ weylSymplecticForm_isAlt := by
  let q := pureCovarianceProductCoordinates d
  let L := sidewiseCutEquiv A B C D
  let P := physicalPhaseSubspace A B
  let S := physicalPhaseSubspace C D
  have hv : (q.auxiliaryCutCovariance P S).compl₁₂ L.toLinearMap L.toLinearMap=
      d.form.compl₁₂ sidewisePhaseEmbedding sidewisePhaseEmbedding := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change q.form (auxiliaryCutMap P S (L x)) (auxiliaryCutMap P S (L y))=_
    rw [pureCovarianceProductCoordinates_form,sidewiseCutEquiv_embedding,sidewiseCutEquiv_embedding]
    rfl
  have ho : (productForm ((weylSymplecticForm (JointConfiguration A B)).restrict P)
      ((weylSymplecticForm (JointConfiguration C D)).restrict S)).compl₁₂ L.toLinearMap L.toLinearMap=
        weylSymplecticForm (JointConfiguration A C) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact sidewiseCutEquiv_weylForm A B C D x y
  have h := bosonFormCost_pullback_general (q.auxiliaryCutCovariance P S)
    (productForm ((weylSymplecticForm (JointConfiguration A B)).restrict P)
      ((weylSymplecticForm (JointConfiguration C D)).restrict S))
    (q.auxiliaryCutCovariance_symmetric P S) (q.auxiliaryCutForm_alternating P S)
    (productForm_nondegenerate (physicalPhaseSubspace_nondegenerate A B)
      (physicalPhaseSubspace_nondegenerate C D)) (q.auxiliaryCut_uncertainty P S) L
    (Module.finBasis ℝ (P×S)) (Module.finBasis ℝ (JointConfiguration A C×JointConfiguration A C))
  exact h.symm.trans (bosonFormCost_congr_forms _ _ _ _ _ hv ho)

end Gaussian.Physical.Boson
