import Gaussian.Physical.Fermion.PurityBridge

/-! Exact doubled pure covariance blocks for canonical thermal parameters.
All square roots include zero at pure endpoints; no inverse mixedness is used. -/
noncomputable section
open Gaussian.Phase
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion

def purificationCross (n : ℕ) (t : Fin n → ℝ) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.diagonal (fun a => Real.sqrt (1-(t a.1)^2))

def purificationBlock (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    Matrix (MajoranaIndex n ⊕ MajoranaIndex n) (MajoranaIndex n ⊕ MajoranaIndex n) ℝ :=
  Matrix.fromBlocks (generatorMatrix (thermal n t ht)) (purificationCross n t)
    (-purificationCross n t) (-generatorMatrix (thermal n t ht))

theorem generatorMatrix_transpose {n : ℕ} (ρ : Density n) :
    (generatorMatrix ρ)ᵀ = -generatorMatrix ρ := by
  ext a b
  simp only [Matrix.transpose_apply,Matrix.neg_apply,generatorMatrix]
  rw [covariance_skew ρ b a]

@[simp] theorem purificationCross_transpose (n : ℕ) (t : Fin n → ℝ) :
    (purificationCross n t)ᵀ = purificationCross n t := by simp [purificationCross]

theorem thermal_generatorMatrix_square (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    generatorMatrix (thermal n t ht)*generatorMatrix (thermal n t ht) =
      Matrix.diagonal (fun a => -(t a.1)^2) := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same,toEuclidean_generatorMatrix]
  apply (EuclideanSpace.basisFun (MajoranaIndex n) ℝ).toBasis.ext
  intro a
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  change covarianceGenerator (thermal n t ht) (covarianceGenerator (thermal n t ht)
    (coefficientBasis n a)) = Matrix.toEuclideanLin
      (Matrix.diagonal (fun a : MajoranaIndex n => -(t a.1)^2)) (coefficientBasis n a)
  rcases a with ⟨i,b⟩
  cases b
  · rw [thermalGenerator_false,map_smul,thermalGenerator_true,smul_smul]
    ext a
    simp [Matrix.toLpLin_apply,coefficientBasis,PiLp.single_apply,pow_two]
    split <;> simp_all
  · rw [thermalGenerator_true,map_smul,thermalGenerator_false,smul_smul]
    ext a
    simp [Matrix.toLpLin_apply,coefficientBasis,PiLp.single_apply,pow_two]
    split <;> simp_all

theorem one_sub_parameter_square_nonneg (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n) : 0≤1-(t i)^2 := by
  have h := mul_nonneg (show 0≤1-t i by linarith [(ht i).2])
    (show 0≤1+t i by linarith [(ht i).1])
  nlinarith

theorem purificationCross_square (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    purificationCross n t*purificationCross n t = Matrix.diagonal (fun a => 1-(t a.1)^2) := by
  rw [purificationCross,Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  nlinarith [Real.sq_sqrt (one_sub_parameter_square_nonneg n t ht a.1)]

theorem thermal_generatorMatrix_commutes_cross (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    generatorMatrix (thermal n t ht)*purificationCross n t =
      purificationCross n t*generatorMatrix (thermal n t ht) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [purificationCross,Matrix.mul_diagonal,Matrix.diagonal_mul,
    generatorMatrix,thermal_covariance]
  by_cases h : i=j
  · subst j; ring
  · simp [h]

theorem thermal_generator_square_sub_cross_square (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    generatorMatrix (thermal n t ht)*generatorMatrix (thermal n t ht) -
      purificationCross n t*purificationCross n t = -1 := by
  rw [thermal_generatorMatrix_square,purificationCross_square n t ht]
  ext a b
  by_cases h : a=b
  · subst b; simp [Matrix.diagonal_apply]; ring
  · simp [Matrix.diagonal_apply,Matrix.one_apply,h]

theorem purificationBlock_square (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    purificationBlock n t ht*purificationBlock n t ht = -1 := by
  unfold purificationBlock
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg,Matrix.neg_mul,neg_neg]
  have hd := thermal_generator_square_sub_cross_square n t ht
  have hc := thermal_generatorMatrix_commutes_cross n t ht
  simp only [sub_eq_add_neg] at hd
  have hd' : -(purificationCross n t * purificationCross n t) +
      generatorMatrix (thermal n t ht) * generatorMatrix (thermal n t ht) = -1 := by
    rw [add_comm,hd]
  rw [hd,hd',hc,add_neg_cancel,neg_add_cancel]
  ext a b
  cases a <;> cases b <;> simp [Matrix.fromBlocks,Matrix.one_apply]

theorem purificationBlock_transpose (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1) :
    (purificationBlock n t ht)ᵀ = -purificationBlock n t ht := by
  unfold purificationBlock
  simp only [Matrix.fromBlocks_transpose,generatorMatrix_transpose,
    Matrix.transpose_neg,purificationCross_transpose,neg_neg]
  ext a b
  cases a <;> cases b <;> simp [Matrix.fromBlocks]

end Gaussian.Physical.Fermion
