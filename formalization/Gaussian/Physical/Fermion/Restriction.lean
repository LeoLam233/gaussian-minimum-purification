import Gaussian.Physical.Fermion.Covariance

/-! Physical prefix restriction, implemented on actual density matrices by an
occupation-basis equivalence and partial trace.  Its covariance restriction is
proved from expectation transport, not built into the definition. -/
noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

/-- Split k complete leading modes from l trailing modes.  The total is written
l+k so recursion in the number retained is definitionally transparent. -/
def occupationSplit : (k l : ℕ) → Occupation (l+k) ≃ Occupation k × Occupation l
  | 0, l =>
    { toFun := fun x => ((),x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by rcases x with ⟨⟨⟩,x⟩; rfl }
  | k+1, l =>
    { toFun := fun x => ((x.1,(occupationSplit k l x.2).1),(occupationSplit k l x.2).2)
      invFun := fun x => (x.1.1,(occupationSplit k l).symm (x.1.2,x.2))
      left_inv := fun x => by simp
      right_inv := fun x => by simp }

/-- Embed an actual observable on the retained modes, with identity on discarded modes. -/
def prefixEmbed (k l : ℕ) (A : Operator k) : Operator (l+k) :=
  (A ⊗ₖ (1 : Operator l)).submatrix (occupationSplit k l) (occupationSplit k l)

/-- An actual reduced density matrix. -/
def prefixRestriction (k l : ℕ) (ρ : Density (l+k)) : Density k :=
  (ρ.relabel (occupationSplit k l).symm).traceRight

theorem prefixEmbed_mul (k l : ℕ) (A B : Operator k) :
    prefixEmbed k l (A * B) = prefixEmbed k l A * prefixEmbed k l B := by
  unfold prefixEmbed
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Restriction is the usual algebraic expectation restriction for genuine embedded observables. -/
theorem prefixRestriction_expectation (k l : ℕ) (ρ : Density (l+k)) (A : Operator k) :
    ((prefixRestriction k l ρ).m * A).trace = (ρ.m * prefixEmbed k l A).trace := by
  change (((ρ.relabel (occupationSplit k l).symm).m).traceRight * A).trace = _
  rw [← Matrix.trace_mul_kron_one_right, MState.relabel_m]
  unfold prefixEmbed
  rw [← Matrix.trace_submatrix _ (occupationSplit k l)]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (occupationSplit k l) _]
  simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- Inclusion of the labels of k complete leading modes. -/
def prefixIndex : (k l : ℕ) → Fin k → Fin (l+k)
  | 0, _, i => Fin.elim0 i
  | k+1, l, i => Fin.cases 0 (fun j => (prefixIndex k l j).succ) i

@[simp] theorem prefixIndex_zero (k l : ℕ) : prefixIndex (k+1) l 0 = 0 := rfl
@[simp] theorem prefixIndex_succ (k l : ℕ) (i : Fin k) :
    prefixIndex (k+1) l i.succ = (prefixIndex k l i).succ := rfl

/-- Entrywise recursive factorization of the physical observable embedding. -/
theorem prefixEmbed_kronecker (k l : ℕ) (A : Matrix Bool Bool ℂ) (B : Operator k) :
    prefixEmbed (k+1) l (A ⊗ₖ B) = A ⊗ₖ prefixEmbed k l B := by
  ext x y
  change (A x.1 y.1 * B (occupationSplit k l x.2).1 (occupationSplit k l y.2).1) *
      (1 : Operator l) (occupationSplit k l x.2).2 (occupationSplit k l y.2).2 =
    A x.1 y.1 * (B (occupationSplit k l x.2).1 (occupationSplit k l y.2).1 *
      (1 : Operator l) (occupationSplit k l x.2).2 (occupationSplit k l y.2).2)
  exact mul_assoc _ _ _

@[simp] theorem prefixEmbed_one (k l : ℕ) : prefixEmbed k l 1 = 1 := by
  simp [prefixEmbed, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- The partial-trace embedding really is the complete-mode CAR embedding. -/
theorem prefixEmbed_majorana (k l : ℕ) (i : Fin k) (b : Bool) :
    prefixEmbed k l (majorana k (i,b)) = majorana (l+k) (prefixIndex k l i,b) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [majorana_zero, prefixEmbed_kronecker, prefixEmbed_one,
        prefixIndex_zero]
      rfl
    · rw [majorana_succ, prefixEmbed_kronecker, ih, prefixIndex_succ]
      rfl

/-- Actual reduced CAR moments yield the restricted covariance entries. -/
theorem prefixRestriction_covariance (k l : ℕ) (ρ : Density (l+k))
    (a b : MajoranaIndex k) :
    covariance (prefixRestriction k l ρ) a b =
      covariance ρ (prefixIndex k l a.1,a.2) (prefixIndex k l b.1,b.2) := by
  unfold covariance
  rw [prefixRestriction_expectation]
  have hsub (A B : Operator k) : prefixEmbed k l (A-B) = prefixEmbed k l A - prefixEmbed k l B := by
    ext x y; simp [prefixEmbed, Matrix.kronecker_apply, sub_mul]
  rw [hsub, prefixEmbed_mul, prefixEmbed_mul, prefixEmbed_majorana, prefixEmbed_majorana]

end Gaussian.Physical.Fermion
