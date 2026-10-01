import Gaussian.Phase.Williamson
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Dimension parity is derived from the raw nondegenerate alternating form,
so reference purification does not require an extra even-dimension hypothesis. -/
noncomputable section
open Module
namespace Gaussian.Phase

/-- A finite real nondegenerate alternating commutator has even dimension,
including the empty coefficient space. -/
theorem even_finrank_of_nondegenerate_alternating {E : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (Ω : LinearMap.BilinForm ℝ E) (ha : Ω.IsAlt) (hn : Ω.Nondegenerate) :
    Even (finrank ℝ E) := by
  let b := Module.finBasis ℝ E
  let M := LinearMap.BilinForm.toMatrix b Ω
  have hm : M.transpose = -M := by
    ext i j
    simp only [M,Matrix.transpose_apply,Matrix.neg_apply,LinearMap.BilinForm.toMatrix_apply]
    exact (ha.neg_eq (b i) (b j)).symm
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hn
  have he := congrArg Matrix.det hm
  rw [Matrix.det_transpose,Matrix.det_neg,Fintype.card_fin] at he
  rcases Nat.even_or_odd (finrank ℝ E) with h | h
  · exact h
  · rw [h.neg_one_pow] at he
    exfalso
    apply hdet
    linarith

end Gaussian.Phase
