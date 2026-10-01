import Gaussian.Physical.Fermion.Restriction
import Gaussian.Physical.Fermion.ParityWick

/-! The actual complementary density, and its signed CAR semantics.  Occupation
partial trace is compared with the trailing CAR algebra only after proving the
Jordan–Wigner parity factors.  Equality of all word moments uses total parity
invariance; even-word and covariance transport require no such assumption. -/
noncomputable section
open scoped Matrix Kronecker
namespace Gaussian.Physical.Fermion

/-- The actual density obtained by tracing out the leading k complete modes. -/
def suffixRestriction (k l : ℕ) (ρ : Density (l+k)) : Density l :=
  (ρ.relabel (occupationSplit k l).symm).traceLeft

/-- Occupation-tensor observable transport.  A trailing odd CAR generator has
`parity k`, rather than identity, in the first argument. -/
def splitTensor (k l : ℕ) (A : Operator k) (B : Operator l) : Operator (l+k) :=
  (A ⊗ₖ B).submatrix (occupationSplit k l) (occupationSplit k l)

theorem splitTensor_mul (k l : ℕ) (A C : Operator k) (B D : Operator l) :
    splitTensor k l (A*C) (B*D) = splitTensor k l A B * splitTensor k l C D := by
  unfold splitTensor
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

@[simp] theorem splitTensor_one (k l : ℕ) : splitTensor k l 1 1 = 1 := by
  simp [splitTensor, Matrix.submatrix_one_equiv]

theorem splitTensor_smul_right (k l : ℕ) (A : Operator k) (B : Operator l) (z : ℂ) :
    splitTensor k l A (z • B) = z • splitTensor k l A B := by
  ext x y
  simp [splitTensor, mul_left_comm]

@[simp] theorem splitTensor_zero (l : ℕ) (B : Operator l) :
    splitTensor 0 l 1 B = B := by
  ext x y
  simp [splitTensor, occupationSplit]

theorem splitTensor_kronecker (k l : ℕ) (A : Matrix Bool Bool ℂ)
    (B : Operator k) (C : Operator l) :
    splitTensor (k+1) l (A ⊗ₖ B) C = A ⊗ₖ splitTensor k l B C := by
  ext x y
  change (A x.1 y.1 * B (occupationSplit k l x.2).1 (occupationSplit k l y.2).1) *
      C (occupationSplit k l x.2).2 (occupationSplit k l y.2).2 =
    A x.1 y.1 * (B (occupationSplit k l x.2).1 (occupationSplit k l y.2).1 *
      C (occupationSplit k l x.2).2 (occupationSplit k l y.2).2)
  exact mul_assoc _ _ _

/-- Total parity factors in the actual occupation representation. -/
theorem splitTensor_parity (k l : ℕ) :
    splitTensor k l (parity k) (parity l) = parity (l+k) := by
  induction k with
  | zero => simp [parity]
  | succ k ih =>
    rw [parity, splitTensor_kronecker, ih]
    rfl

/-- Inclusion of all trailing complete-mode labels, in their original order. -/
def suffixIndex : (k l : ℕ) → Fin l → Fin (l+k)
  | 0, _, i => i
  | k+1, l, i => (suffixIndex k l i).succ

@[simp] theorem suffixIndex_zero (l : ℕ) (i : Fin l) : suffixIndex 0 l i = i := rfl
@[simp] theorem suffixIndex_succ (k l : ℕ) (i : Fin l) :
    suffixIndex (k+1) l i = (suffixIndex k l i).succ := rfl

theorem suffixIndex_val (k l : ℕ) (i : Fin l) : (suffixIndex k l i).val = k+i.val := by
  induction k with
  | zero => simp
  | succ k ih => simp only [suffixIndex_succ, Fin.val_succ, ih]; omega

theorem suffixIndex_injective (k l : ℕ) : Function.Injective (suffixIndex k l) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [suffixIndex_val, suffixIndex_val] at hv
  omega

/-- The physical trailing Majorana contains every leading-mode parity factor. -/
theorem suffixMajorana_factor (k l : ℕ) (i : Fin l) (b : Bool) :
    majorana (l+k) (suffixIndex k l i,b) =
      splitTensor k l (parity k) (majorana l (i,b)) := by
  induction k with
  | zero => simp [parity]
  | succ k ih =>
    change oneParity ⊗ₖ majorana (l+k) (suffixIndex k l i,b) = _
    rw [ih, parity, splitTensor_kronecker]

/-- A word of r trailing global Majoranas carries the actual leading parity to
power r.  This identity precedes, and justifies, all restriction statements. -/
theorem suffixWord_factor (k l : ℕ) (w : List (MajoranaIndex l)) :
    wordOperator (l+k) (w.map (fun a => (suffixIndex k l a.1,a.2))) =
      splitTensor k l ((parity k)^w.length) (wordOperator l w) := by
  induction w with
  | nil => simp [wordOperator]
  | cons a w ih =>
    rw [List.map_cons, wordOperator_cons, suffixMajorana_factor, ih,
      ← splitTensor_mul, List.length_cons, pow_succ', wordOperator_cons]

/-- Partial trace transports ordinary occupation-tensor expectations. -/
theorem suffixRestriction_expectation (k l : ℕ) (ρ : Density (l+k)) (A : Operator l) :
    ((suffixRestriction k l ρ).m * A).trace = (ρ.m * splitTensor k l 1 A).trace := by
  change (((ρ.relabel (occupationSplit k l).symm).m).traceLeft * A).trace = _
  rw [← Matrix.trace_mul_one_kron_right, MState.relabel_m]
  unfold splitTensor
  rw [← Matrix.trace_submatrix _ (occupationSplit k l)]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (occupationSplit k l) _]
  simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

theorem parity_pow_even (k r : ℕ) (hr : Even r) : (parity k)^r = 1 := by
  obtain ⟨s,hs⟩ := hr
  rw [hs, ← two_mul, pow_mul, pow_two, parity_square, one_pow]

/-- Even-word restriction holds without a parity hypothesis on the state. -/
theorem suffixRestriction_even_moment (k l : ℕ) (ρ : Density (l+k))
    (w : List (MajoranaIndex l)) (hw : Even w.length) :
    moment (suffixRestriction k l ρ) w =
      moment ρ (w.map (fun a => (suffixIndex k l a.1,a.2))) := by
  unfold moment
  rw [suffixRestriction_expectation, suffixWord_factor, parity_pow_even k _ hw]

/-- Odd ordinary suffix words are also odd under the full physical parity. -/
theorem splitTensor_word_parity (k l : ℕ) (w : List (MajoranaIndex l)) :
    parity (l+k) * splitTensor k l 1 (wordOperator l w) * parity (l+k) =
      (-1 : ℂ)^w.length • splitTensor k l 1 (wordOperator l w) := by
  rw [← splitTensor_parity, ← splitTensor_mul, ← splitTensor_mul,
    Matrix.mul_one, parity_square, wordOperator_parity, splitTensor_smul_right]

theorem suffixRestriction_moment_parity (k l : ℕ) (ρ : Density (l+k))
    (hρ : ParityInvariant ρ) (w : List (MajoranaIndex l)) :
    moment (suffixRestriction k l ρ) w =
      (-1 : ℂ)^w.length * moment (suffixRestriction k l ρ) w := by
  unfold moment
  rw [suffixRestriction_expectation]
  nth_rw 1 [← hρ]
  rw [trace_conjugate_product, splitTensor_word_parity, Matrix.mul_smul, Matrix.trace_smul]
  rfl

theorem suffixRestriction_odd_moment (k l : ℕ) (ρ : Density (l+k))
    (hρ : ParityInvariant ρ) (w : List (MajoranaIndex l)) (hw : Odd w.length) :
    moment (suffixRestriction k l ρ) w = 0 := by
  have h := suffixRestriction_moment_parity k l ρ hρ w
  rw [hw.neg_one_pow, neg_one_mul] at h
  have hm : (2 : ℂ) * moment (suffixRestriction k l ρ) w = 0 := by linear_combination h
  exact (mul_eq_zero.mp hm).resolve_left (by norm_num)

/-- The actual complementary density inherits total parity invariance. -/
theorem suffixRestriction_parityInvariant (k l : ℕ) (ρ : Density (l+k))
    (hρ : ParityInvariant ρ) : ParityInvariant (suffixRestriction k l ρ) := by
  apply parityInvariant_of_odd_moments
  exact suffixRestriction_odd_moment k l ρ hρ

/-- Full signed CAR restriction, proved for all lengths, including repeated
labels.  Only the odd case requires parity invariance of the global density. -/
theorem suffixRestriction_moment (k l : ℕ) (ρ : Density (l+k))
    (hρ : ParityInvariant ρ) (w : List (MajoranaIndex l)) :
    moment (suffixRestriction k l ρ) w =
      moment ρ (w.map (fun a => (suffixIndex k l a.1,a.2))) := by
  rcases Nat.even_or_odd w.length with hw | hw
  · exact suffixRestriction_even_moment k l ρ w hw
  · rw [suffixRestriction_odd_moment k l ρ hρ w hw,
      moment_odd_zero ρ hρ _ (by simpa only [List.length_map] using hw)]

/-- Covariance transport is a consequence of the physical even-word identity. -/
theorem suffixRestriction_covariance (k l : ℕ) (ρ : Density (l+k))
    (a b : MajoranaIndex l) :
    covariance (suffixRestriction k l ρ) a b =
      covariance ρ (suffixIndex k l a.1,a.2) (suffixIndex k l b.1,b.2) := by
  rw [covariance_eq_im_twoPoint, covariance_eq_im_twoPoint,
    suffixRestriction_even_moment k l ρ [a,b] (by change Even (2 : ℕ); decide)]
  rfl

/-- The raw Wick condition survives the actual complementary partial trace. -/
theorem isQuasifree_suffixRestriction (k l : ℕ) (ρ : Density (l+k)) (hρ : IsQuasifree ρ) :
    IsQuasifree (suffixRestriction k l ρ) := by
  apply isQuasifree_of_wick
  intro w
  rw [suffixRestriction_moment k l ρ hρ.1, hρ.2, wickValue_map]
  congr 1
  funext a b
  exact (suffixRestriction_moment k l ρ hρ.1 [a,b]).symm

/-- Genuine pure-state complementary entropy equality.  No Gaussian,
nonemptiness-of-a-cut, or positive-parity assumption is imposed. -/
theorem suffixRestriction_entropy_eq_prefixRestriction (k l : ℕ) (ρ : Density (l+k))
    (hρ : ∃ ψ, ρ = MState.pure ψ) :
    Sᵥₙ (suffixRestriction k l ρ) = Sᵥₙ (prefixRestriction k l ρ) := by
  obtain ⟨ψ,rfl⟩ := hρ
  exact _root_.Sᵥₙ_pure_complement ψ (occupationSplit k l).symm

/-- Both total parity components of a pure quasifree state obey the same
complementary entropy theorem. -/
theorem pureQuasifree_suffix_entropy (k l : ℕ) (ρ : Density (l+k)) (hρ : IsPureQuasifree ρ) :
    Sᵥₙ (suffixRestriction k l ρ) = Sᵥₙ (prefixRestriction k l ρ) :=
  suffixRestriction_entropy_eq_prefixRestriction k l ρ hρ.2

end Gaussian.Physical.Fermion
