import Gaussian.Attainment.PairCompactness

/-! Actual finite auxiliary-frame covariance/form compression attainment.
This keeps both restricted forms. Gaussian state-orbit identification is separate. -/
noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace
namespace Gaussian.Attainment

theorem complexFrame_coisometry {k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M))
    (hv : Orthonormal ℝ v) : complexFrame v * (complexFrame v).conjTranspose = 1 := by
  ext i j
  have h := (orthonormal_iff_ite.mp hv) i j
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, complexFrame,
    Complex.star_def, Complex.conj_ofReal, Matrix.one_apply]
  have hh : (∑ x, (v i) x * (v j) x : ℝ) = if i=j then 1 else 0 := by
    simpa only [mul_comm] using h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal hh

theorem cutEmbedding_coisometry {a k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M))
    (hv : Orthonormal ℝ v) :
    cutEmbedding (a := a) v * (cutEmbedding (a := a) v).conjTranspose = 1 := by
  simp [cutEmbedding, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    complexFrame_coisometry v hv, Matrix.fromBlocks_one]

theorem rectangular_conj_posDef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (V : HermitianMat n ℂ) (hV : V.mat.PosDef)
    (B : Matrix m n ℂ) (hB : B*B.conjTranspose = 1) : (V.conj B).mat.PosDef := by
  have hinj : Function.Injective B.conjTranspose.mulVec := by
    intro x y hxy
    have h := congrArg B.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  simpa only [Matrix.conjTranspose_conjTranspose, HermitianMat.conj_apply_mat] using
    hV.conjTranspose_mul_mul_same hinj

def bosonCutCost {a k M : ℕ} (V O : HermitianMat (Fin a ⊕ Fin M) ℂ)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : ℝ :=
  bosonPairCost (V.conj (cutEmbedding (a := a) v)) (O.conj (cutEmbedding (a := a) v))

/-- Exact finite-reference cut minimum, without any uniform squeezing assumption.
An admissible cut is supplied, not a presumed compact symplectic frame locus. -/
theorem exists_boson_cut_minimum {a k M : ℕ}
    (V O : HermitianMat (Fin a ⊕ Fin M) ℂ) (hV : V.mat.PosDef)
    (v₀ : Fin k → EuclideanSpace ℝ (Fin M)) (hv₀ : v₀ ∈ frameSet)
    (hO₀ : (O.conj (cutEmbedding (a := a) v₀)).mat.det ≠ 0) :
    ∃ v ∈ frameSet (ι := Fin k) (E := EuclideanSpace ℝ (Fin M)),
      (O.conj (cutEmbedding (a := a) v)).mat.det ≠ 0 ∧
      ∀ w : Fin k → EuclideanSpace ℝ (Fin M), w ∈ frameSet → (O.conj (cutEmbedding (a := a) w)).mat.det ≠ 0 →
        bosonCutCost V O v ≤ bosonCutCost V O w := by
  exact exists_bosonPairCost_minimum frameSet (frameSet_compact)
    (fun v => V.conj (cutEmbedding (a := a) v))
    (fun v => O.conj (cutEmbedding (a := a) v))
    (V.continuous_conj.comp continuous_cutEmbedding)
    (O.continuous_conj.comp continuous_cutEmbedding)
    (fun v hv => rectangular_conj_posDef V hV _ (cutEmbedding_coisometry v hv)) v₀ hv₀ hO₀

end Gaussian.Attainment
