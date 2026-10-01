import Gaussian.Phase.BosonicPurificationDomain
import Gaussian.Phase.BosonicPurificationSubcuts
import Gaussian.Phase.BosonicPurificationCutComplementary

/-! Actual changes of auxiliary allocation inside the raw covariance domain.
Every move has a proved integer count and nonincreasing actual cut cost. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

def withSplit (p : BosonicCovariancePurifier V Ω M) (S : Submodule ℝ p.Auxiliary)
    (hS : (p.commutator.restrict S).Nondegenerate) : BosonicCovariancePurifier V Ω M :=
  { p with split := S, split_nondegenerate := hS }

def complement (p : BosonicCovariancePurifier V Ω M) : BosonicCovariancePurifier V Ω M :=
  p.withSplit (p.commutator.orthogonal p.split)
    (symplectic_complement_data p.commutator p.alternating p.nondegenerate
      p.split p.split_nondegenerate).2

@[simp] theorem complement_leftModes (p : BosonicCovariancePurifier V Ω M) :
    p.complement.leftModes=p.rightModes := by
  change finrank ℝ (p.commutator.orthogonal p.split)/2=p.rightModes
  rw [p.rightModes_dimension]
  omega

@[simp] theorem complement_rightModes (p : BosonicCovariancePurifier V Ω M) :
    p.complement.rightModes=p.leftModes := by
  change M-p.complement.leftModes=p.leftModes
  rw [p.complement_leftModes]
  have h:=p.sideModes_sum
  omega

theorem complement_cost (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate) :
    p.complement.cost (Ω.orthogonal A) = p.cost A :=
  (p.covariance.auxiliaryCutCost_complementary hΩa p.alternating hΩn p.nondegenerate
    A p.split hA p.split_nondegenerate).symm

/-- An excess selected side can give one complete mode to the other side at
nonincreasing cost, on the actual same-total covariance domain. -/
theorem exists_move_left (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes+1=p.leftModes ∧ q.cost A ≤ p.cost A := by
  obtain ⟨P,hPd,hPn,hWn,hPc,hWd,hcost,hpure⟩ := p.covariance.exists_auxiliary_subcut_selection
    hΩa p.alternating A p.split hA p.split_nondegenerate
    (by simpa only [p.leftModes_dimension] using hExcess)
  let S := ((p.commutator.restrict p.split).orthogonal P).map p.split.subtype
  have hS : (p.commutator.restrict S).Nondegenerate :=
    PureCompatibleCovariance.auxiliary_subcut_nondegenerate p.split _ hWn
  let q := p.withSplit S hS
  refine ⟨q,?_,hcost⟩
  have hdim : finrank ℝ S = finrank ℝ p.split-2 := by
    rw [Submodule.finrank_map_subtype_eq,hWd]
  have htwo : 2 ≤ finrank ℝ p.split := by
    have h:=P.finrank_le
    omega
  change finrank ℝ S/2+1=p.leftModes
  rw [hdim,p.leftModes_dimension]
  rw [p.leftModes_dimension] at htwo
  omega

/-- An excess opposite side can give one complete mode to the selected side;
complementary covariance cost equality supplies the exact objective transport. -/
theorem exists_move_right (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ (Ω.orthogonal A) < 2*p.rightModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes=p.leftModes+1 ∧ q.cost A ≤ p.cost A := by
  have hB := (symplectic_complement_data Ω hΩa hΩn A hA).2
  obtain ⟨r,hr,hcost⟩ := p.complement.exists_move_left hΩa (Ω.orthogonal A) hB
    (by simpa using hExcess)
  refine ⟨r.complement,?_,?_⟩
  · rw [complement_leftModes] at hr ⊢
    have hp := p.sideModes_sum
    have hr' := r.sideModes_sum
    omega
  · have hrc := r.complement_cost hΩa hΩn (Ω.orthogonal A) hB
    rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩa.isRefl A] at hrc
    exact hrc.trans_le (hcost.trans_eq (p.complement_cost hΩa hΩn A hA))

end BosonicCovariancePurifier
end Gaussian.Phase
