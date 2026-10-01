import Gaussian.Phase.CompatibleGeometry

/-! Canonical initial real coordinate modes and their actual orthogonal
complements. No physical-state or entropy interface is imported. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

/-- The canonical real coordinate frame for the first a modes. -/
def initialModeVectors {N : ℕ} (a : ℕ) (h : a ≤ N) :
    Fin a × Bool → EuclideanSpace ℝ (Fin N × Bool) :=
  fun i => EuclideanSpace.basisFun (Fin N × Bool) ℝ (Fin.castLE h i.1,i.2)

/-- The span of the first a standard real two-coordinate modes. -/
def initialModeSubspace {N : ℕ} (a : ℕ) (h : a ≤ N) :
    Submodule ℝ (EuclideanSpace ℝ (Fin N × Bool)) :=
  Submodule.span ℝ (Set.range (initialModeVectors a h))

/-- The truncated coordinate frame is orthonormal, including the empty frame. -/
theorem initialModeVectors_orthonormal {N : ℕ} (a : ℕ) (h : a ≤ N) :
    Orthonormal ℝ (initialModeVectors a h) := by
  apply (EuclideanSpace.basisFun (Fin N × Bool) ℝ).orthonormal.comp
    (fun i : Fin a × Bool => (Fin.castLE h i.1,i.2))
  intro x y hxy
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun z : Fin N × Bool => z.1.val) hxy
  · exact congrArg (fun z : Fin N × Bool => z.2) hxy

/-- Each mode contributes exactly two real dimensions. -/
theorem finrank_initialModeSubspace {N : ℕ} (a : ℕ) (h : a ≤ N) :
    finrank ℝ (initialModeSubspace a h) = 2*a := by
  unfold initialModeSubspace
  rw [finrank_span_eq_card (initialModeVectors_orthonormal a h).linearIndependent,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  omega

/-- A terminal standard vector is orthogonal to all protected initial modes
when the protected modes stop before the terminal index. -/
theorem terminal_mem_initialModeSubspace_orthogonal {k a : ℕ}
    (h : a ≤ k+1) (ha : a ≤ k) (b : Bool) :
    EuclideanSpace.basisFun (Fin (k+1) × Bool) ℝ (Fin.last k,b) ∈
      (initialModeSubspace a h)ᗮ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    have hne : (Fin.castLE h i.1,i.2) ≠ (Fin.last k,b) := by
      intro he
      have hv := congrArg (fun z : Fin (k+1) × Bool => z.1.val) he
      have hi := i.1.isLt
      dsimp at hv
      omega
    exact (orthonormal_iff_ite.mp
      (EuclideanSpace.basisFun (Fin (k+1) × Bool) ℝ).orthonormal
      (Fin.castLE h i.1,i.2) (Fin.last k,b)).trans (by simp [hne])
  | zero => simp
  | add x y hx hy hx' hy' => simp only [inner_add_left,hx',hy',add_zero]
  | smul r x hx hx' => simp only [inner_smul_left,hx',mul_zero]

/-- Mode-count excess gives exactly the real dimension inequality needed for
invariant-plane selection inside the actual protected orthogonal complement. -/
theorem initialModeSubspace_orthogonal_excess {N : ℕ} (a : ℕ) (h : a ≤ N)
    (hexcess : 2*a < N) :
    finrank ℝ (EuclideanSpace ℝ (Fin N × Bool)) <
      2 * finrank ℝ (initialModeSubspace a h)ᗮ := by
  have hA := finrank_initialModeSubspace a h
  have hsplit := (initialModeSubspace a h).finrank_add_finrank_orthogonal
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin N × Bool)) = 2*N := by
    rw [finrank_euclideanSpace,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  omega

end Gaussian.Phase
