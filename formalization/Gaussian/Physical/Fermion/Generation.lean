import Gaussian.Physical.Fermion.Quasifree

/-! Faithfulness of the explicit finite CAR matrix representation. -/
noncomputable section
open scoped Matrix Kronecker BigOperators
namespace Gaussian.Physical.Fermion
set_option backward.isDefEq.respectTransparency false

def tailEmbedding (n : ℕ) : Operator n →ₐ[ℂ] Operator (n+1) where
  toFun A := (1 : Matrix Bool Bool ℂ) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' := Matrix.kronecker_add _
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul, Matrix.one_kronecker_one]

@[simp] theorem tailEmbedding_apply (n : ℕ) (A : Operator n) :
    tailEmbedding n A = (1 : Matrix Bool Bool ℂ) ⊗ₖ A := rfl

theorem oneParity_majorana_product :
    oneParity = (-Complex.I) • (oneMajorana false * oneMajorana true) := by
  ext a b
  cases a <;> cases b <;> simp [oneParity, oneMajorana, Matrix.mul_apply]

theorem boolMatrix_pauli (A : Matrix Bool Bool ℂ) :
    A = ((A false false + A true true)/2) • 1 +
      ((A false true + A true false)/2) • oneMajorana false +
      (Complex.I * (A false true - A true false)/2) • oneMajorana true +
      ((A false false - A true true)/2) • oneParity := by
  ext a b
  cases a <;> cases b <;>
    simp [oneMajorana, oneParity, Matrix.add_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem matrix_bool_blocks {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix (Bool × d) (Bool × d) ℂ) :
    A = ∑ a : Bool, ∑ b : Bool,
      (Matrix.single a b (1 : ℂ)) ⊗ₖ (fun i j => A (a,i) (b,j)) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  cases a <;> cases b <;> simp [Matrix.sum_apply, Matrix.single_apply, Matrix.kroneckerMap_apply]

theorem majoranas_generate (n : ℕ) (S : Subalgebra ℂ (Operator n))
    (h : ∀ a, majorana n a ∈ S) : ∀ A : Operator n, A ∈ S := by
  induction n with
  | zero =>
    intro A
    have he : A = algebraMap ℂ (Operator 0) (A () ()) := by
      ext a b; cases a; cases b; simp [Algebra.algebraMap_eq_smul_one]
    rw [he]
    exact S.algebraMap_mem _
  | succ n ih =>
    have hx : oneMajorana false ⊗ₖ (1 : Operator n) ∈ S := h (0,false)
    have hy : oneMajorana true ⊗ₖ (1 : Operator n) ∈ S := h (0,true)
    have hz : oneParity ⊗ₖ (1 : Operator n) ∈ S := by
      rw [oneParity_majorana_product, Matrix.smul_kronecker,
        ← Matrix.one_mul (1 : Operator n), Matrix.mul_kronecker_mul]
      exact S.smul_mem (S.mul_mem hx hy) _
    have htgen (a : MajoranaIndex n) : tailEmbedding n (majorana n a) ∈ S := by
      change (1 : Matrix Bool Bool ℂ) ⊗ₖ majorana n a ∈ S
      have htail : oneParity ⊗ₖ majorana n a ∈ S := h (a.1.succ,a.2)
      have hm := S.mul_mem hz htail
      simpa only [tailEmbedding_apply, ← Matrix.mul_kronecker_mul, oneParity_square, Matrix.one_mul] using hm
    have ht (A : Operator n) : (1 : Matrix Bool Bool ℂ) ⊗ₖ A ∈ S :=
      ih (S.comap (tailEmbedding n)) htgen A
    have hh (A : Matrix Bool Bool ℂ) : A ⊗ₖ (1 : Operator n) ∈ S := by
      rw [boolMatrix_pauli A]
      simp only [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]
      exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem S.one_mem _)
        (S.smul_mem hx _)) (S.smul_mem hy _)) (S.smul_mem hz _)
    intro A
    rw [matrix_bool_blocks A]
    apply S.sum_mem
    intro a _
    apply S.sum_mem
    intro b _
    have hm := S.mul_mem (hh (Matrix.single a b 1)) (ht (fun i j => A (a,i) (b,j)))
    simpa only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one] using hm

theorem adjoin_majoranas_eq_top (n : ℕ) :
    Algebra.adjoin ℂ (Set.range (majorana n)) = ⊤ := by
  apply top_unique
  intro A _
  exact majoranas_generate n (Algebra.adjoin ℂ (Set.range (majorana n)))
    (fun a => Algebra.subset_adjoin (Set.mem_range_self a)) A

theorem closure_majoranas_word (n : ℕ) {A : Operator n}
    (hA : A ∈ Submonoid.closure (Set.range (majorana n))) :
    ∃ l, wordOperator n l = A := by
  induction hA using Submonoid.closure_induction with
  | mem A hA =>
    rcases hA with ⟨a,rfl⟩
    exact ⟨[a],by simp [wordOperator]⟩
  | one => exact ⟨[],rfl⟩
  | mul A B _ _ hA hB =>
    rcases hA with ⟨a,rfl⟩
    rcases hB with ⟨b,rfl⟩
    exact ⟨a++b, by simp [wordOperator]⟩

theorem span_words_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (wordOperator n)) = ⊤ := by
  apply top_unique
  have hs : (⊤ : Submodule ℂ (Operator n)) =
      Submodule.span ℂ (Submonoid.closure (Set.range (majorana n)) : Set (Operator n)) := by
    rw [← Algebra.adjoin_eq_span, adjoin_majoranas_eq_top]
    rfl
  rw [hs]
  apply Submodule.span_le.mpr
  intro A hA
  obtain ⟨l,rfl⟩ := closure_majoranas_word n hA
  exact Submodule.subset_span ⟨l,rfl⟩

theorem density_eq_of_moments {n : ℕ} (ρ σ : Density n)
    (h : ∀ l, moment ρ l = moment σ l) : ρ = σ := by
  have ht (A : Operator n) : (ρ.m * A).trace = (σ.m * A).trace := by
    have hA : A ∈ Submodule.span ℂ (Set.range (wordOperator n)) := by
      rw [span_words_eq_top]; trivial
    induction hA using Submodule.span_induction with
    | mem A hA => rcases hA with ⟨l,rfl⟩; exact h l
    | zero => simp
    | add A B _ _ hA hB => simp only [Matrix.mul_add, Matrix.trace_add, hA,hB]
    | smul r A _ hA => simp only [Matrix.mul_smul, Matrix.trace_smul, hA]
  apply MState.ext_m
  ext i j
  simpa only [Matrix.trace_mul_single, MulOpposite.op_one, one_smul] using
    ht (Matrix.single j i 1)

theorem quasifree_eq_of_twoPoint {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (h₂ : ∀ a b, moment ρ [a,b] = moment σ [a,b]) : ρ = σ :=
  density_eq_of_moments ρ σ (quasifree_moments_determined ρ σ hρ hσ h₂)

end Gaussian.Physical.Fermion
