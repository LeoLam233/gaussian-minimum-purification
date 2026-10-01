import Gaussian.Physical.Fermion.CutEntropy

/-! Actual four-party complete-mode purification domain.  The AA' marginal is
a genuine graded CAR mode reordering followed by the actual density partial trace;
no unsigned occupation permutation substitutes for the CAR implementation. -/
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Label the physical A,B modes first, then auxiliary A',B' modes. -/
def fourModeEquiv (a b c d : ℕ) :
    ((Fin a ⊕ Fin b) ⊕ (Fin c ⊕ Fin d)) ≃ Fin ((c+d)+(a+b)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm (a+b) (c+d))))

/-- The complete-mode permutation from A,B,A',B' order to A,A',B,B' order. -/
def sidewiseModePermutation (nA nB mA mB : ℕ) :
    Equiv.Perm (Fin ((mA+mB)+(nA+nB))) :=
  (fourModeEquiv nA nB mA mB).symm.trans
    ((Equiv.sumSumSumComm (Fin nA) (Fin nB) (Fin mA) (Fin mB)).trans
      ((fourModeEquiv nA mA nB mB).trans (finCongr (by omega))))

/-- The permutation acts on whole pairs of Majoranas, without splitting a mode. -/
def sidewiseRotation (nA nB mA mB : ℕ) :
    CoefficientSpace ((mA+mB)+(nA+nB)) ≃ₗᵢ[ℝ] CoefficientSpace ((mA+mB)+(nA+nB)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr (sidewiseModePermutation nA nB mA mB) (Equiv.refl Bool))

/-- An actual signed CAR unitary implementing the complete-mode permutation. -/
def sidewiseUnitary (nA nB mA mB : ℕ) :
    Matrix.unitaryGroup (Occupation ((mA+mB)+(nA+nB))) ℂ :=
  Classical.choose (orthogonal_implemented _ (sidewiseRotation nA nB mA mB))

theorem sidewiseUnitary_implements (nA nB mA mB : ℕ) :
    Implements ((mA+mB)+(nA+nB)) (sidewiseRotation nA nB mA mB)
      (sidewiseUnitary nA nB mA mB) :=
  Classical.choose_spec (orthogonal_implemented _ (sidewiseRotation nA nB mA mB))

/-- Actual AA' density marginal in the stated four-party ordering. -/
def sidewiseRestriction (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) : Density (nA+mA) :=
  selectedRestriction (nA+mA) (nB+mB) (by omega) (sidewiseUnitary nA nB mA mB) σ

/-- The ordinary von Neumann entropy of the actual AA' marginal. -/
def sidewiseEntropy (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) : ℝ := Sᵥₙ (sidewiseRestriction nA nB mA mB σ)

/-- The raw physical feasible class, with fixed AB density and both pure total parities. -/
def IsSidewisePurifier (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) : Prop :=
  IsPureQuasifree σ ∧ prefixRestriction (nA+nB) (mA+mB) σ=ρ

@[fun_prop] theorem continuous_sidewiseEntropy (nA nB mA mB : ℕ) :
    Continuous (sidewiseEntropy nA nB mA mB) :=
  continuous_selectedEntropy (nA+mA) (nB+mB) _ _

theorem sidewiseRestriction_isQuasifree (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsQuasifree σ) :
    IsQuasifree (sidewiseRestriction nA nB mA mB σ) :=
  selectedRestriction_isQuasifree _ _ _ σ hσ _ _ (sidewiseUnitary_implements nA nB mA mB)

theorem sidewiseEntropy_eq_hermitianCost (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) (hσ : IsQuasifree σ) :
    sidewiseEntropy nA nB mA mB σ =
      Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat (sidewiseRestriction nA nB mA mB σ)) :=
  quasifree_entropy_eq_hermitianCost _ _ (sidewiseRestriction_isQuasifree nA nB mA mB σ hσ)

/-- Genuine entropy attainment in each nonempty fixed sidewise mode-count domain. -/
theorem exists_sidewise_minimum (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (hne : ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ) :
    ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ ∧
      ∀ τ,IsSidewisePurifier nA nB mA mB ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB mA mB τ := by
  obtain ⟨σ,hσ,hm,hmin⟩ := exists_minimum_quasifreePurifiers (nA+nB) (mA+mB) ρ hne
    (sidewiseEntropy nA nB mA mB) (continuous_sidewiseEntropy nA nB mA mB)
  exact ⟨σ,⟨hσ,hm⟩,fun τ hτ => hmin τ hτ.1 hτ.2⟩

end Gaussian.Physical.Fermion
