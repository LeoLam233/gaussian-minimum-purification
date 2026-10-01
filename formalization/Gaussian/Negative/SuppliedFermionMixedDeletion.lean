import Gaussian.Negative.PreservedEntropyMixedDeletion
import Gaussian.Physical.Fermion.ModeRelabel

/-! Exact supplied three-mode N1 fermionic fixture, with the noncontiguous
retained subsystem obtained by a genuine signed CAR mode relabeling. -/
set_option autoImplicit false
noncomputable section
open Gaussian.Phase Gaussian.Physical.Fermion
open scoped RealInnerProductSpace Matrix
namespace Gaussian.Negative

def suppliedRotationEntry (a b : MajoranaIndex 3) : ℝ :=
  if a.1=2 ∨ b.1=2 then if a=b then 1 else 0 else
    if a.2=b.2 then if a.1=b.1 then fixtureC else
      if a.1=0 then (if a.2 then -fixtureS else fixtureS)
      else (if a.2 then fixtureS else -fixtureS) else 0

def suppliedColumn (b : MajoranaIndex 3) : CoefficientSpace 3 :=
  WithLp.toLp 2 (fun a => suppliedRotationEntry a b)

theorem suppliedColumn_orthonormal : Orthonormal ℝ suppliedColumn := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,b⟩ ⟨j,d⟩
  simp only [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;> cases b <;> cases d <;>
    simp [suppliedColumn,suppliedRotationEntry,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
    nlinarith [fixtureCS_norm]

def suppliedRotation : CoefficientSpace 3 ≃ₗᵢ[ℝ] CoefficientSpace 3 :=
  let f := orthonormalFrameIsometry suppliedColumn suppliedColumn_orthonormal
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

theorem suppliedRotation_basis (a : MajoranaIndex 3) :
    suppliedRotation (coefficientBasis 3 a)=suppliedColumn a :=
  orthonormalFrameIsometry_single suppliedColumn suppliedColumn_orthonormal a

theorem suppliedRotation_matrix : coefficientMatrix suppliedRotation=suppliedRotationEntry := by
  ext a b
  rw [coefficientMatrix_entry,suppliedRotation_basis]
  rfl

theorem suppliedRotation_inverse_basis (a b : MajoranaIndex 3) :
    (suppliedRotation⁻¹ (coefficientBasis 3 a)) b=suppliedRotationEntry a b := by
  rw [← coefficientMatrix_entry,← coefficientMatrix_transpose,suppliedRotation_matrix]
  rfl

def suppliedParameter : Fin 3 → ℝ := ![1,1/2,1]
theorem suppliedParameter_mem (i : Fin 3) : suppliedParameter i∈Set.Icc (-1:ℝ) 1 := by
  fin_cases i <;> norm_num [suppliedParameter]

def suppliedUnitary : Matrix.unitaryGroup (Occupation 3) ℂ :=
  Classical.choose (orthogonal_implemented 3 suppliedRotation)
theorem suppliedUnitary_implements : Implements 3 suppliedRotation suppliedUnitary :=
  Classical.choose_spec (orthogonal_implemented 3 suppliedRotation)

def suppliedFermionFixture : Density 3 := (thermal 3 suppliedParameter suppliedParameter_mem).uConj suppliedUnitary

theorem suppliedFermionFixture_isQuasifree : IsQuasifree suppliedFermionFixture :=
  isQuasifree_unitary_of_implements 3 _ (thermal_isQuasifree _ _ _) _ _ suppliedUnitary_implements

/-- The exact matrix displayed in N1: blocks ε/2, X/√2, −X/√2, 0, and ε. -/
def suppliedCovariance (a b : MajoranaIndex 3) : ℝ :=
  if a.1=b.1 then
    if a.1=0 then (if a.2=b.2 then 0 else if a.2 then -(1/2:ℝ) else 1/2)
    else if a.1=2 then (if a.2=b.2 then 0 else if a.2 then -1 else 1) else 0
  else if a.1=0 ∧ b.1=1 then (if a.2=b.2 then 0 else 1/Real.sqrt 2)
  else if a.1=1 ∧ b.1=0 then (if a.2=b.2 then 0 else -(1/Real.sqrt 2)) else 0

theorem suppliedFermionFixture_covariance (a b : MajoranaIndex 3) :
    covariance suppliedFermionFixture a b=suppliedCovariance a b := by
  rw [suppliedFermionFixture,implemented_covariance _ _ suppliedUnitary suppliedUnitary_implements]
  simp_rw [suppliedRotation_inverse_basis]
  have hcross : (3/2:ℝ)*fixtureC*fixtureS=(Real.sqrt 2)⁻¹ := by simpa only [one_div] using fixture_cross_exact
  rcases a with ⟨i,c⟩
  rcases b with ⟨j,d⟩
  fin_cases i <;> fin_cases j <;> cases c <;> cases d <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,thermal_covariance,
      suppliedRotationEntry,suppliedParameter,suppliedCovariance,← fixture_cross_exact] <;>
    nlinarith [fixtureC_sq,fixtureS_sq,hcross]

/-- Graded complete-mode move to the order (A,C_pure,C_bad). -/
def suppliedReordered : Density 3 :=
  actualModeRelabel (Equiv.swap (1 : Fin 3) 2) suppliedFermionFixture

def suppliedRetained : Density 2 := prefixRestriction 2 1 suppliedReordered

def suppliedDeleted : Density 1 := suffixRestriction 2 1 suppliedReordered

theorem suppliedReordered_isQuasifree : IsQuasifree suppliedReordered :=
  actualModeRelabel_isQuasifree _ _ suppliedFermionFixture_isQuasifree

theorem suppliedRetained_eq_thermal :
    suppliedRetained=thermal 2 ![1/2,1] (by intro i; fin_cases i <;> norm_num) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction _ _ _ suppliedReordered_isQuasifree) (thermal_isQuasifree _ _ _)
  rintro ⟨i,a⟩ ⟨j,b⟩
  change covariance (prefixRestriction 2 1 suppliedReordered) (i,a) (j,b)=_
  rw [prefixRestriction_covariance,suppliedReordered,actualModeRelabel_covariance,
    suppliedFermionFixture_covariance,thermal_covariance]
  have hp0 : prefixIndex 2 1 0=(0 : Fin 3) := by apply Fin.ext; rfl
  have hp1 : prefixIndex 2 1 1=(1 : Fin 3) := by apply Fin.ext; rfl
  fin_cases i <;> fin_cases j <;> cases a <;> cases b <;>
    norm_num [suppliedCovariance,hp0,hp1,Equiv.swap_apply_def]

theorem suppliedDeleted_eq_thermal :
    suppliedDeleted=thermal 1 (fun _ => 0) (by intro i; norm_num) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_suffixRestriction _ _ _ suppliedReordered_isQuasifree) (thermal_isQuasifree _ _ _)
  rintro ⟨i,a⟩ ⟨j,b⟩
  change covariance (suffixRestriction 2 1 suppliedReordered) (i,a) (j,b)=_
  rw [suffixRestriction_covariance,suppliedReordered,actualModeRelabel_covariance,
    suppliedFermionFixture_covariance,thermal_covariance]
  fin_cases i; fin_cases j
  cases a <;> cases b <;>
    norm_num [suppliedCovariance,suffixIndex,Equiv.swap_apply_def]

theorem suppliedFermionFixture_entropy_preserved : Sᵥₙ suppliedRetained=Sᵥₙ suppliedFermionFixture := by
  rw [suppliedRetained_eq_thermal,suppliedFermionFixture,unitaryState_entropy,
    entropy_thermal,entropy_thermal]
  simp [Fin.sum_univ_succ,suppliedParameter]

theorem suppliedDeleted_not_pure : ¬∃ ψ,suppliedDeleted=MState.pure ψ := by
  rw [suppliedDeleted_eq_thermal,thermal_pure_iff_endpoints]
  intro h
  have h0 := h 0
  norm_num at h0

theorem suppliedFermionFixture_cross_ne_zero :
    covariance suppliedFermionFixture (0,false) (1,true)≠0 := by
  rw [suppliedFermionFixture_covariance]
  norm_num [suppliedCovariance]

end Gaussian.Negative
