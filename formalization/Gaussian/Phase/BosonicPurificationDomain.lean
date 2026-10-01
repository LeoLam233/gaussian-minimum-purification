import Gaussian.Phase.BosonicPurificationCuts

/-! The actual finite covariance purification domain. Its fields are raw finite
symplectic data, a constructed pure covariance, an exact physical restriction,
and an actual nondegenerate auxiliary split. No minimum, cost equality, spectrum,
state realization or entropy theorem is a field of this domain. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A finite raw bosonic covariance purification with exactly M auxiliary modes. -/
structure BosonicCovariancePurifier (V Ω : LinearMap.BilinForm ℝ E) (M : ℕ) where
  (Auxiliary : Type u)
  [auxAdd : AddCommGroup Auxiliary]
  [auxModule : Module ℝ Auxiliary]
  [auxFinite : FiniteDimensional ℝ Auxiliary]
  commutator : LinearMap.BilinForm ℝ Auxiliary
  alternating : commutator.IsAlt
  nondegenerate : commutator.Nondegenerate
  mode_count : finrank ℝ Auxiliary = 2*M
  covariance : PureCompatibleCovariance (productForm Ω commutator)
  physical : ∀ x y, covariance.form (x,0) (y,0) = V x y
  split : Submodule ℝ Auxiliary
  split_nondegenerate : (commutator.restrict split).Nondegenerate

attribute [instance] BosonicCovariancePurifier.auxAdd BosonicCovariancePurifier.auxModule
  BosonicCovariancePurifier.auxFinite

namespace BosonicCovariancePurifier
variable {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

/-- The actual covariance cut cost, with both restricted forms retained. -/
def cost (p : BosonicCovariancePurifier V Ω M) (A : Submodule ℝ E) : ℝ :=
  p.covariance.auxiliaryCutCost A p.split

def leftModes (p : BosonicCovariancePurifier V Ω M) : ℕ := finrank ℝ p.split / 2

def rightModes (p : BosonicCovariancePurifier V Ω M) : ℕ := M-p.leftModes

theorem leftModes_dimension (p : BosonicCovariancePurifier V Ω M) :
    finrank ℝ p.split = 2*p.leftModes := by
  obtain ⟨a,ha⟩ := even_finrank_of_nondegenerate_alternating (p.commutator.restrict p.split)
    (fun x => p.alternating x) p.split_nondegenerate
  unfold leftModes
  omega

theorem leftModes_le (p : BosonicCovariancePurifier V Ω M) : p.leftModes ≤ M := by
  have h := p.split.finrank_le
  rw [p.mode_count,p.leftModes_dimension] at h
  omega

theorem rightModes_dimension (p : BosonicCovariancePurifier V Ω M) :
    finrank ℝ (p.commutator.orthogonal p.split) = 2*p.rightModes := by
  rw [LinearMap.BilinForm.finrank_orthogonal p.nondegenerate,p.mode_count,p.leftModes_dimension]
  unfold rightModes
  omega

theorem sideModes_sum (p : BosonicCovariancePurifier V Ω M) : p.leftModes+p.rightModes=M := by
  have h := p.leftModes_le
  unfold rightModes
  omega

/-- Every domain point is transported to literal finite canonical sidewise
coordinates, with mode counts, original physical covariance and actual cost
all preserved. This prevents the reference parametrization from imposing an
unproved fixed-coordinate optimization restriction. -/
theorem exists_canonical_sidewise_transport (p : BosonicCovariancePurifier V Ω M)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate) :
    ∃ a b : ℕ, a+b=M ∧ a=p.leftModes ∧ b=p.rightModes ∧
      ∃ q : PureCompatibleCovariance
        (productForm Ω (productForm (standardSymplecticForm (EuclideanSpace ℝ (Fin a)))
          (standardSymplecticForm (EuclideanSpace ℝ (Fin b))))),
        (∀ x y, q.form (x,0) (y,0) = V x y) ∧
        q.auxiliaryCutCost A (LinearMap.inl ℝ (StandardBosonicSpace a) (StandardBosonicSpace b)).range =
          p.cost A := by
  obtain ⟨a,b,ha,hb,hM,Q,hQ,hQL,hQR⟩ := exists_canonical_auxiliary_split
    p.commutator p.alternating p.nondegenerate p.split p.split_nondegenerate
  have hab : a+b=M := by rw [p.mode_count] at hM; omega
  have ha' : a=p.leftModes := by rw [p.leftModes_dimension] at ha; omega
  have hb' : b=p.rightModes := by have h:=p.sideModes_sum; omega
  let τ := productForm (standardSymplecticForm (EuclideanSpace ℝ (Fin a)))
    (standardSymplecticForm (EuclideanSpace ℝ (Fin b)))
  let T := (LinearMap.inl ℝ (StandardBosonicSpace a) (StandardBosonicSpace b)).range
  let q := p.covariance.pullbackAuxiliary Q hQ
  have hT : (τ.restrict T).Nondegenerate := by
    apply symplectic_range_nondegenerate
      (standardSymplecticForm (EuclideanSpace ℝ (Fin a))) τ
      (standardPureCovariance (EuclideanSpace ℝ (Fin a))).commutator_nondegenerate
      (LinearMap.inl ℝ (StandardBosonicSpace a) (StandardBosonicSpace b))
    intro x y
    simp [τ]
  have hmap : T.map Q.toLinearMap = p.split := by
    rw [← LinearMap.range_comp]
    exact hQL
  refine ⟨a,b,hab,ha',hb',q,?_,?_⟩
  · intro x y
    change (p.covariance.pullbackAuxiliary Q hQ).form (x,0) (y,0) = V x y
    rw [PureCompatibleCovariance.pullbackAuxiliary_physical,p.physical]
  · change (p.covariance.pullbackAuxiliary Q hQ).auxiliaryCutCost A T = p.cost A
    rw [PureCompatibleCovariance.auxiliaryCutCost_pullbackAuxiliary _ Q hQ A T hA hT,hmap]
    rfl

end BosonicCovariancePurifier
end Gaussian.Phase
