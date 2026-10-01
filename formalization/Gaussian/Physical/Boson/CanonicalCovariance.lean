import Gaussian.Physical.Boson.CanonicalConfiguration

/-! The explicit paired diagonal covariance on canonical finite configurations. -/
noncomputable section
namespace Gaussian.Physical.Boson
open Matrix
open scoped RealInnerProductSpace

def diagonalAmplitude {n : ℕ} (ν : Fin n → ℝ) :
    CanonicalConfiguration n →ₗ[ℝ] CanonicalConfiguration n :=
  Matrix.toEuclideanLin (Matrix.diagonal ν)

@[simp] theorem diagonalAmplitude_apply {n : ℕ} (ν : Fin n → ℝ)
    (x : CanonicalConfiguration n) (i : Fin n) : diagonalAmplitude ν x i=ν i*x i := by
  change (Matrix.diagonal ν *ᵥ x) i=ν i*x i
  simp only [Matrix.mulVec_diagonal]

def canonicalCovariance {n : ℕ} (ν : Fin n → ℝ) :
    LinearMap.BilinForm ℝ (CanonicalConfiguration n × CanonicalConfiguration n) :=
  (innerₗ (CanonicalConfiguration n)).compl₁₂
      (LinearMap.fst ℝ _ _) ((diagonalAmplitude ν).comp (LinearMap.fst ℝ _ _)) +
    (innerₗ (CanonicalConfiguration n)).compl₁₂
      (LinearMap.snd ℝ _ _) ((diagonalAmplitude ν).comp (LinearMap.snd ℝ _ _))

@[simp] theorem canonicalCovariance_apply {n : ℕ} (ν : Fin n → ℝ)
    (z w : CanonicalConfiguration n × CanonicalConfiguration n) :
    canonicalCovariance ν z w = ∑ i : Fin n, ν i*(z.1 i*w.1 i+z.2 i*w.2 i) := by
  change ⟪z.1,diagonalAmplitude ν w.1⟫+⟪z.2,diagonalAmplitude ν w.2⟫=_
  rw [PiLp.inner_apply,PiLp.inner_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [inner,diagonalAmplitude_apply] <;> ring

lemma canonicalCovariance_symm {n : ℕ} (ν : Fin n → ℝ) : (canonicalCovariance ν).IsSymm := by
  constructor
  intro z w
  rw [canonicalCovariance_apply,canonicalCovariance_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma canonicalCovariance_quadratic {n : ℕ} (ν : Fin n → ℝ)
    (q p : CanonicalConfiguration n) :
    canonicalCovariance ν (q,p) (q,p) = ∑ i : Fin n, ν i*((q i)^2+(p i)^2) := by
  rw [canonicalCovariance_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Gaussian.Physical.Boson
