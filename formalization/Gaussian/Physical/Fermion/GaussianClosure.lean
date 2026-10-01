import Gaussian.Physical.Fermion.PairedCovariance
import Gaussian.Physical.Fermion.LocalAction

noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

theorem unitaryState_compose {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U V : Matrix.unitaryGroup d ℂ) :
    (ρ.uConj V).uConj U = ρ.uConj (U*V) := by
  apply MState.ext_m
  change (U : Matrix d d ℂ)*((V : Matrix d d ℂ)*ρ.m*(V : Matrix d d ℂ)ᴴ)*(U : Matrix d d ℂ)ᴴ =
    ((U : Matrix d d ℂ)*(V : Matrix d d ℂ))*ρ.m*((U : Matrix d d ℂ)*(V : Matrix d d ℂ))ᴴ
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- The proved full physical orthogonal action preserves the raw Wick feasible class. -/
theorem isQuasifree_unitary_of_implements (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    IsQuasifree (ρ.uConj U) := by
  obtain ⟨t,ht,S,V,hpos,hV,rfl⟩ := exists_quasifree_state_normal_form n ρ hρ
  rw [unitaryState_compose]
  exact rotated_thermal_isQuasifree n t ht (R*S) (U*V) (implements_mul n hU hV)

/-- Actual complete-mode density restriction preserves the raw Wick predicate. -/
theorem isQuasifree_prefixRestriction (k l : ℕ) (ρ : Density (l+k)) (hρ : IsQuasifree ρ) :
    IsQuasifree (prefixRestriction k l ρ) := by
  apply isQuasifree_of_wick
  intro w
  rw [prefixRestriction_moment,hρ.2,wickValue_map]
  congr 1
  funext a b
  exact (prefixRestriction_moment k l ρ [a,b]).symm

/-- Arbitrary finite orthogonal mode selection followed by actual density
partial trace remains an admissible finite parity-invariant quasifree state. -/
theorem isQuasifree_orthogonalRestriction (k l : ℕ) (ρ : Density (l+k)) (hρ : IsQuasifree ρ)
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U) :
    IsQuasifree (prefixRestriction k l (ρ.uConj U)) :=
  isQuasifree_prefixRestriction k l _ (isQuasifree_unitary_of_implements (l+k) ρ hρ R U hU)

end Gaussian.Physical.Fermion
