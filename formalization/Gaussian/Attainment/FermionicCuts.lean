import Gaussian.Attainment.Frames
import Gaussian.Entropy.Scalar
import QuantumInfo.Entropy.VonNeumann

/-! Continuous actual Hermitian matrix-compression objective over finite auxiliary
cut frames. This is a covariance-level attainment ingredient, not a state-orbit theorem. -/
noncomputable section
namespace Gaussian.Attainment

/-- Spectral functional on an independently supplied Hermitian matrix. For CAR the
matrix to be supplied is iΓ, after proving the physical covariance bridge. -/
def fermionHermitianCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMat ι ℂ) : ℝ := (A.cfc (fun x => Gaussian.Entropy.fermion |x|)).trace / 2

theorem continuous_fermionHermitianCost {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fermionHermitianCost (ι := ι)) := by
  unfold fermionHermitianCost
  have hf : Continuous (fun x : ℝ => Gaussian.Entropy.fermion |x|) :=
    Gaussian.Entropy.continuous_fermion.comp continuous_abs
  exact (HermitianMat.trace_Continuous.comp (HermitianMat.cfc_continuous hf)).div_const 2

theorem fermionHermitianCost_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMat ι ℂ) :
    fermionHermitianCost A = (∑ i, Gaussian.Entropy.fermion |A.H.eigenvalues i|)/2 := by
  rw [fermionHermitianCost, HermitianMat.trace_cfc_eq]

/-- Complexified real auxiliary frame, with no replacement by complex cut subspaces. -/
def complexFrame {k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    Matrix (Fin k) (Fin M) ℂ := fun i j => ((v i) j : ℂ)

theorem continuous_complexFrame {k M : ℕ} : Continuous (complexFrame (k := k) (M := M)) := by
  unfold complexFrame
  fun_prop

/-- The physical party is held fixed while only the auxiliary cut frame changes. -/
def cutEmbedding {a k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin M) ℂ :=
  Matrix.fromBlocks 1 0 0 (complexFrame v)

theorem continuous_cutEmbedding {a k M : ℕ} :
    Continuous (cutEmbedding (a := a) (k := k) (M := M)) := by
  unfold cutEmbedding complexFrame
  fun_prop

def fermionCutCost {a k M : ℕ} (A : HermitianMat (Fin a ⊕ Fin M) ℂ)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : ℝ :=
  fermionHermitianCost (A.conj (cutEmbedding (a := a) v))

theorem continuous_fermionCutCost {a k M : ℕ} (A : HermitianMat (Fin a ⊕ Fin M) ℂ) :
    Continuous (fermionCutCost (k := k) A) :=
  continuous_fermionHermitianCost.comp (A.continuous_conj.comp continuous_cutEmbedding)

theorem frameSet_nonempty {k M : ℕ} (h : k ≤ M) :
    (frameSet (ι := Fin k) (E := EuclideanSpace ℝ (Fin M))).Nonempty := by
  refine ⟨fun i => EuclideanSpace.basisFun (Fin M) ℝ (Fin.castLE h i),?_⟩
  exact (EuclideanSpace.basisFun (Fin M) ℝ).orthonormal.comp (Fin.castLE h) (Fin.castLE_injective h)

/-- A genuine minimizer of the fixed-reference finite CAR spectral cut objective.
To identify this with Gaussian purification, state realization and full auxiliary orbit
surjectivity remain separate, mandatory theorems. Dimensions here count real coefficients. -/
theorem exists_fermion_cut_minimum {a k M : ℕ} (h : k ≤ M)
    (A : HermitianMat (Fin a ⊕ Fin M) ℂ) :
    ∃ v ∈ frameSet (ι := Fin k) (E := EuclideanSpace ℝ (Fin M)),
      ∀ w : Fin k → EuclideanSpace ℝ (Fin M), w ∈ frameSet → fermionCutCost A v ≤ fermionCutCost A w :=
  exists_minimum_on_frames (frameSet_nonempty h) _ (continuous_fermionCutCost A).continuousOn
end Gaussian.Attainment
