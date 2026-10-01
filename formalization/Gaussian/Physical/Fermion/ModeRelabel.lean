import Gaussian.Physical.Fermion.ModeSelection
import Gaussian.Physical.Fermion.SidewiseCountTransport

/-! Relabel complete CAR modes through a proved actual unitary implementation.
This is not the unsigned occupation-basis permutation. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion

def completeModeRotation {n : ℕ} (p : Equiv.Perm (Fin n)) :
    CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr p (Equiv.refl Bool))

def completeModeUnitary {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Matrix.unitaryGroup (Occupation n) ℂ :=
  Classical.choose (orthogonal_implemented n (completeModeRotation p))

theorem completeModeUnitary_implements {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Implements n (completeModeRotation p) (completeModeUnitary p) :=
  Classical.choose_spec (orthogonal_implemented n (completeModeRotation p))

theorem modeEquiv_count {n m : ℕ} (e : Fin n ≃ Fin m) : n=m := by
  simpa using Fintype.card_congr e

def actualModeRelabel {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : Density n) : Density m :=
  modeCountCast (modeEquiv_count e)
    (ρ.uConj (completeModeUnitary (e.trans (finCongr (modeEquiv_count e).symm))))

theorem actualModeRelabel_covariance {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : Density n)
    (a b : MajoranaIndex m) :
    covariance (actualModeRelabel e ρ) a b = covariance ρ (e.symm a.1,a.2) (e.symm b.1,b.2) := by
  rw [actualModeRelabel,modeCountCast_covariance,
    permutationAction_covariance _ _ _ (completeModeUnitary_implements _) ]
  congr 1

theorem actualModeRelabel_isQuasifree {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : Density n) (hρ : IsQuasifree ρ) : IsQuasifree (actualModeRelabel e ρ) :=
  modeCountCast_isQuasifree _ _ (isQuasifree_unitary_of_implements n ρ hρ _ _
    (completeModeUnitary_implements _))

theorem actualModeRelabel_isPureQuasifree {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : Density n) (hρ : IsPureQuasifree ρ) : IsPureQuasifree (actualModeRelabel e ρ) :=
  modeCountCast_isPureQuasifree _ _ ⟨isQuasifree_unitary_of_implements n ρ hρ.1 _ _
    (completeModeUnitary_implements _),(unitaryState_pure_iff ρ _).mpr hρ.2⟩

theorem actualModeRelabel_entropy {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : Density n) :
    Sᵥₙ (actualModeRelabel e ρ)=Sᵥₙ ρ := by
  rw [actualModeRelabel,modeCountCast_entropy,unitaryState_entropy]

theorem actualModeRelabel_symm {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : Density n)
    (hρ : IsQuasifree ρ) : actualModeRelabel e.symm (actualModeRelabel e ρ)=ρ := by
  apply quasifree_eq_of_covariance _ _
    (actualModeRelabel_isQuasifree _ _ (actualModeRelabel_isQuasifree e ρ hρ)) hρ
  intro a b
  simp only [actualModeRelabel_covariance,Equiv.symm_symm,Equiv.symm_apply_apply]

end Gaussian.Physical.Fermion
