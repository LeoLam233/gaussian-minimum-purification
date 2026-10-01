import Gaussian.Physical.Fermion.SidewiseCountTransport
import Gaussian.Physical.Fermion.ModeSelection

/-! Coherent transport of actual states, unitaries and real CAR actions along
mode-count equalities. These are arithmetic identifications, never mode swaps. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

def unitaryCountCast {n m : ℕ} (h : n=m) (U : Matrix.unitaryGroup (Occupation n) ℂ) :
    Matrix.unitaryGroup (Occupation m) ℂ := h ▸ U

def orthogonalCountCast {n m : ℕ} (h : n=m)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n) :
    CoefficientSpace m ≃ₗᵢ[ℝ] CoefficientSpace m := h ▸ R

def coefficientCountEquiv {n m : ℕ} (h : n=m) : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace m :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr (finCongr h) (Equiv.refl Bool))

@[simp] theorem coefficientCountEquiv_rfl {n : ℕ} (v : CoefficientSpace n) :
    coefficientCountEquiv rfl v=v := by ext a; rfl

@[simp] theorem coefficientCountEquiv_basis {n m : ℕ} (h : n=m) (a : MajoranaIndex n) :
    coefficientCountEquiv h (coefficientBasis n a)=coefficientBasis m (Fin.cast h a.1,a.2) := by
  rcases a with ⟨i,b⟩
  simp [coefficientCountEquiv,coefficientBasis,reindexCoefficient_single]

@[simp] theorem unitaryCountCast_rfl {n : ℕ} (U : Matrix.unitaryGroup (Occupation n) ℂ) :
    unitaryCountCast rfl U=U := rfl

@[simp] theorem unitaryCountCast_trans {n m l : ℕ} (h : n=m) (g : m=l)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) :
    unitaryCountCast g (unitaryCountCast h U)=unitaryCountCast (h.trans g) U := by
  subst m; subst l; rfl

@[simp] theorem modeCountCast_unitaryState {n m : ℕ} (h : n=m) (ρ : Density n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) :
    modeCountCast h (ρ.uConj U)=(modeCountCast h ρ).uConj (unitaryCountCast h U) := by
  subst m; rfl

theorem implements_countCast {n m : ℕ} (h : n=m)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    Implements m (orthogonalCountCast h R) (unitaryCountCast h U) := by
  subst m; exact hU

theorem orthogonalCountCast_fix_iff {n m : ℕ} (h : n=m)
    (R : CoefficientSpace m ≃ₗᵢ[ℝ] CoefficientSpace m) (v : CoefficientSpace n) :
    orthogonalCountCast h.symm R v=v ↔ R (coefficientCountEquiv h v)=coefficientCountEquiv h v := by
  subst m
  simp only [orthogonalCountCast,coefficientCountEquiv_rfl]

/-- The actual retained density coheres with a change only in the notation for its count. -/
theorem prefixRestriction_cast_retained_eq {n k K l : ℕ} (h : k=K)
    (hk : n=l+k) (hK : n=l+K) (ρ : Density n) :
    modeCountCast h (prefixRestriction k l (modeCountCast hk ρ))=
      prefixRestriction K l (modeCountCast hK ρ) := by
  subst K; rfl

@[simp] theorem unitaryState_one (n : ℕ) (ρ : Density n) : ρ.uConj 1=ρ := by
  apply MState.ext_m
  change (1 : Operator n)*ρ.m*(1 : Operator n)ᴴ=ρ.m
  simp

theorem unitaryState_conjugated_action (n : ℕ) (ρ : Density n)
    (S V : Matrix.unitaryGroup (Occupation n) ℂ) :
    (ρ.uConj (S⁻¹*V*S)).uConj S=(ρ.uConj S).uConj V := by
  rw [unitaryState_compose,unitaryState_compose]
  congr 1
  simp [mul_assoc]

end Gaussian.Physical.Fermion
