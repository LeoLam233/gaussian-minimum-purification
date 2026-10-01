import Gaussian.Physical.Fermion.CoefficientOrthogonality
import Gaussian.Physical.Fermion.SuffixRestriction
import Gaussian.Physical.Fermion.ThermalPurity
import Gaussian.Phase.ProtectedFrameSelection

/-! The nontrivial two-mode block of the supplied N1 fixture. A pure third
factor can be appended; the mixed deleted mode already refutes the claimed
arbitrary entropy-preserving deletion implication on this block. -/
set_option autoImplicit false
noncomputable section
open Gaussian.Phase Gaussian.Physical.Fermion
open scoped RealInnerProductSpace Matrix
namespace Gaussian.Negative

def fixtureRotationEntry (c s : ℝ) (a b : MajoranaIndex 2) : ℝ :=
  if a.2=b.2 then
    if a.1=b.1 then c else
      if a.1=0 then (if a.2 then -s else s) else (if a.2 then s else -s)
  else 0

def fixtureColumn (c s : ℝ) (b : MajoranaIndex 2) : CoefficientSpace 2 :=
  WithLp.toLp 2 (fun a => fixtureRotationEntry c s a b)

theorem fixtureColumn_orthonormal (c s : ℝ) (hcs : c^2+s^2=1) :
    Orthonormal ℝ (fixtureColumn c s) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,b⟩ ⟨j,d⟩
  simp only [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;> cases b <;> cases d <;>
    simp [fixtureColumn,fixtureRotationEntry,PiLp.inner_apply,Fintype.sum_prod_type,Fin.sum_univ_two] <;>
    nlinarith

def fixtureRotation (c s : ℝ) (hcs : c^2+s^2=1) :
    CoefficientSpace 2 ≃ₗᵢ[ℝ] CoefficientSpace 2 :=
  let f := orthonormalFrameIsometry (fixtureColumn c s) (fixtureColumn_orthonormal c s hcs)
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

theorem fixtureRotation_basis (c s : ℝ) (hcs : c^2+s^2=1) (a : MajoranaIndex 2) :
    fixtureRotation c s hcs (coefficientBasis 2 a)=fixtureColumn c s a :=
  orthonormalFrameIsometry_single (fixtureColumn c s) (fixtureColumn_orthonormal c s hcs) a

theorem fixtureRotation_matrix (c s : ℝ) (hcs : c^2+s^2=1) :
    coefficientMatrix (fixtureRotation c s hcs)=fixtureRotationEntry c s := by
  ext a b
  rw [coefficientMatrix_entry,fixtureRotation_basis]
  rfl

theorem fixtureRotation_inverse_basis (c s : ℝ) (hcs : c^2+s^2=1) (a b : MajoranaIndex 2) :
    ((fixtureRotation c s hcs)⁻¹ (coefficientBasis 2 a)) b=fixtureRotationEntry c s a b := by
  rw [← coefficientMatrix_entry,← coefficientMatrix_transpose,fixtureRotation_matrix]
  rfl

def fixtureThermalParameter : Fin 2 → ℝ := ![1,1/2]

theorem fixtureThermalParameter_mem (i : Fin 2) : fixtureThermalParameter i∈Set.Icc (-1:ℝ) 1 := by
  fin_cases i <;> norm_num [fixtureThermalParameter]

theorem fixture_first_covariance (c s : ℝ) (hcs : c^2+s^2=1)
    (hc : c^2=2/3) (hs : s^2=1/3)
    (U : Matrix.unitaryGroup (Occupation 2) ℂ) (hU : Implements 2 (fixtureRotation c s hcs) U)
    (a b : Bool) :
    covariance ((thermal 2 fixtureThermalParameter fixtureThermalParameter_mem).uConj U) (0,a) (0,b)=
      if a=b then 0 else if a then -(1/2:ℝ) else 1/2 := by
  rw [implemented_covariance _ _ U hU]
  simp_rw [fixtureRotation_inverse_basis]
  cases a <;> cases b <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,thermal_covariance,
      fixtureRotationEntry,fixtureThermalParameter] <;> nlinarith

theorem fixture_second_covariance (c s : ℝ) (hcs : c^2+s^2=1)
    (hc : c^2=2/3) (hs : s^2=1/3)
    (U : Matrix.unitaryGroup (Occupation 2) ℂ) (hU : Implements 2 (fixtureRotation c s hcs) U)
    (a b : Bool) :
    covariance ((thermal 2 fixtureThermalParameter fixtureThermalParameter_mem).uConj U) (1,a) (1,b)=0 := by
  rw [implemented_covariance _ _ U hU]
  simp_rw [fixtureRotation_inverse_basis]
  cases a <;> cases b <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,thermal_covariance,
      fixtureRotationEntry,fixtureThermalParameter] <;> nlinarith

theorem fixture_cross_covariance (c s : ℝ) (hcs : c^2+s^2=1)
    (U : Matrix.unitaryGroup (Occupation 2) ℂ) (hU : Implements 2 (fixtureRotation c s hcs) U) :
    covariance ((thermal 2 fixtureThermalParameter fixtureThermalParameter_mem).uConj U) (0,false) (1,true)=
      (3/2:ℝ)*c*s := by
  rw [implemented_covariance _ _ U hU]
  simp_rw [fixtureRotation_inverse_basis]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,thermal_covariance,
    fixtureRotationEntry,fixtureThermalParameter]
  ring

/-- Exact algebraic rotation parameters, including their positive signs. -/
def fixtureC : ℝ := Real.sqrt (2/3)
def fixtureS : ℝ := Real.sqrt (1/3)

theorem fixtureC_sq : fixtureC^2=2/3 := Real.sq_sqrt (by norm_num)
theorem fixtureS_sq : fixtureS^2=1/3 := Real.sq_sqrt (by norm_num)
theorem fixtureCS_norm : fixtureC^2+fixtureS^2=1 := by rw [fixtureC_sq,fixtureS_sq]; norm_num

def fixtureUnitary : Matrix.unitaryGroup (Occupation 2) ℂ :=
  Classical.choose (orthogonal_implemented 2 (fixtureRotation fixtureC fixtureS fixtureCS_norm))

theorem fixtureUnitary_implements : Implements 2 (fixtureRotation fixtureC fixtureS fixtureCS_norm) fixtureUnitary :=
  Classical.choose_spec (orthogonal_implemented 2 (fixtureRotation fixtureC fixtureS fixtureCS_norm))

/-- An actual normalized positive density matrix, built from a genuine thermal
state and a proved CAR implementation of a real orthogonal rotation. -/
def mixedDeletionFixture : Density 2 :=
  (thermal 2 fixtureThermalParameter fixtureThermalParameter_mem).uConj fixtureUnitary

theorem mixedDeletionFixture_isQuasifree : IsQuasifree mixedDeletionFixture :=
  isQuasifree_unitary_of_implements 2 _ (thermal_isQuasifree _ _ _) _ _ fixtureUnitary_implements

theorem mixedDeletionFixture_retained :
    prefixRestriction 1 1 mixedDeletionFixture =
      thermal 1 (fun _ => 1/2) (by intro i; norm_num) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_prefixRestriction _ _ _ mixedDeletionFixture_isQuasifree) (thermal_isQuasifree _ _ _)
  rintro ⟨i,a⟩ ⟨j,b⟩
  fin_cases i; fin_cases j
  rw [prefixRestriction_covariance]
  change covariance mixedDeletionFixture (0,a) (0,b)=_
  rw [mixedDeletionFixture,fixture_first_covariance fixtureC fixtureS fixtureCS_norm fixtureC_sq fixtureS_sq
    fixtureUnitary fixtureUnitary_implements,thermal_covariance]
  simp

theorem mixedDeletionFixture_deleted :
    suffixRestriction 1 1 mixedDeletionFixture =
      thermal 1 (fun _ => 0) (by intro i; norm_num) := by
  apply quasifree_eq_of_covariance _ _
    (isQuasifree_suffixRestriction _ _ _ mixedDeletionFixture_isQuasifree) (thermal_isQuasifree _ _ _)
  rintro ⟨i,a⟩ ⟨j,b⟩
  fin_cases i; fin_cases j
  rw [suffixRestriction_covariance]
  change covariance mixedDeletionFixture (1,a) (1,b)=_
  rw [mixedDeletionFixture,fixture_second_covariance fixtureC fixtureS fixtureCS_norm fixtureC_sq fixtureS_sq
    fixtureUnitary fixtureUnitary_implements,thermal_covariance]
  simp

/-- This complete-mode deletion preserves the actual von Neumann entropy exactly. -/
theorem mixedDeletionFixture_entropy_preserved :
    Sᵥₙ (prefixRestriction 1 1 mixedDeletionFixture)=Sᵥₙ mixedDeletionFixture := by
  rw [mixedDeletionFixture_retained]
  change Sᵥₙ (thermal 1 (fun _ => 1/2) _) =
    Sᵥₙ ((thermal 2 fixtureThermalParameter fixtureThermalParameter_mem).uConj fixtureUnitary)
  rw [unitaryState_entropy,entropy_thermal,entropy_thermal]
  simp [Fin.sum_univ_two,fixtureThermalParameter]

/-- The actually deleted CAR marginal is maximally mixed, and is not a pure state. -/
theorem mixedDeletionFixture_deleted_not_pure :
    ¬ ∃ ψ,suffixRestriction 1 1 mixedDeletionFixture=MState.pure ψ := by
  rw [mixedDeletionFixture_deleted,thermal_pure_iff_endpoints]
  intro h
  have h0 := h 0
  norm_num at h0

theorem fixture_cross_exact : (3/2:ℝ)*fixtureC*fixtureS=1/Real.sqrt 2 := by
  have hc : 0<fixtureC := Real.sqrt_pos.mpr (by norm_num)
  have hs : 0<fixtureS := Real.sqrt_pos.mpr (by norm_num)
  have htwo : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have htwoPos : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hp : (fixtureC*fixtureS)^2=2/9 := by rw [mul_pow,fixtureC_sq,fixtureS_sq]; norm_num
  apply (eq_div_iff (ne_of_gt htwoPos)).mpr
  have hq : ((3/2:ℝ)*fixtureC*fixtureS*Real.sqrt 2)^2=1 := by
    calc
      _ = (3/2:ℝ)^2*(fixtureC*fixtureS)^2*(Real.sqrt 2)^2 := by ring
      _ = 1 := by rw [hp,htwo]; norm_num
  nlinarith [mul_pos hc hs,mul_pos (mul_pos hc hs) htwoPos]

/-- The mixed deleted mode is correlated with the retained one, with exactly
the nonzero entry supplied in the contract's N1 fermionic fixture. -/
theorem mixedDeletionFixture_cross :
    covariance mixedDeletionFixture (0,false) (1,true)=1/Real.sqrt 2 := by
  exact (fixture_cross_covariance fixtureC fixtureS fixtureCS_norm fixtureUnitary
    fixtureUnitary_implements).trans fixture_cross_exact

theorem mixedDeletionFixture_cross_ne_zero :
    covariance mixedDeletionFixture (0,false) (1,true)≠0 := by
  rw [mixedDeletionFixture_cross]
  exact div_ne_zero one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- Kernel-checked negative test: entropy-preserving arbitrary complete-mode
deletion need not remove a pure factor. No unproved realizability premise occurs. -/
theorem exists_entropy_preserving_mixed_deletion :
    ∃ ρ : Density 2,IsQuasifree ρ ∧
      Sᵥₙ (prefixRestriction 1 1 ρ)=Sᵥₙ ρ ∧
      (¬ ∃ ψ,suffixRestriction 1 1 ρ=MState.pure ψ) ∧
      covariance ρ (0,false) (1,true)≠0 :=
  ⟨mixedDeletionFixture,mixedDeletionFixture_isQuasifree,mixedDeletionFixture_entropy_preserved,
    mixedDeletionFixture_deleted_not_pure,mixedDeletionFixture_cross_ne_zero⟩

end Gaussian.Negative
