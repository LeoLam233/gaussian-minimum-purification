import Gaussian.Phase.BosonicPurificationCoefficients
import Gaussian.Attainment.BosonicCuts

/-! Compact attainment for the actual restricted covariance/form pair on real
auxiliary frames. The fixed physical block and both compressed forms are
identified with the independently defined Hermitian objective. -/
noncomputable section
open Module Gaussian.Spectral
open Gaussian.Attainment
open scoped Matrix ComplexOrder
namespace Gaussian.Phase

def realReferenceCutMatrix {a k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin M) ℝ :=
  Matrix.fromBlocks 1 0 0 (fun i j => (v i) j)

/-- The literal real coefficient embedding of a variable auxiliary frame,
with identity on every protected physical coefficient. -/
def referenceFrameEmbedding {a k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    ((Fin a ⊕ Fin k) → ℝ) →ₗ[ℝ] ((Fin a ⊕ Fin M) → ℝ) :=
  Matrix.toLin (Pi.basisFun ℝ (Fin a ⊕ Fin k)) (Pi.basisFun ℝ (Fin a ⊕ Fin M))
    (realReferenceCutMatrix (a := a) v).transpose

theorem referenceFrameEmbedding_matrix {a k M : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    (complexifyMatrix (LinearMap.toMatrix (Pi.basisFun ℝ (Fin a ⊕ Fin k))
      (Pi.basisFun ℝ (Fin a ⊕ Fin M)) (referenceFrameEmbedding v))).conjTranspose =
        cutEmbedding (a := a) v := by
  rw [referenceFrameEmbedding,LinearMap.toMatrix_toLin,complexifyMatrix_conjTranspose,
    Matrix.transpose_transpose]
  ext i j
  cases i <;> cases j <;> simp [realReferenceCutMatrix,cutEmbedding,complexFrame,complexifyMatrix,Matrix.fromBlocks,Matrix.one_apply,apply_ite]

def referenceFrameCovariance {a k M : ℕ}
    (V : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin M) → ℝ))
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin k) → ℝ) :=
  V.compl₁₂ (referenceFrameEmbedding v) (referenceFrameEmbedding v)

def referenceFrameCost {a k M : ℕ}
    (V Ω : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin M) → ℝ)) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : ℝ :=
  bosonFormCost (Pi.basisFun ℝ (Fin a ⊕ Fin k)) (referenceFrameCovariance V v)
    (referenceFrameCovariance Ω v)
    ⟨fun x y => hV.eq (referenceFrameEmbedding v x) (referenceFrameEmbedding v y)⟩
    (fun x => hΩ (referenceFrameEmbedding v x))

/-- The actual two restricted forms give exactly the previously proved compact
Hermitian-pair cut objective; the identity is not a defining axiom. -/
theorem referenceFrameCost_eq {a k M : ℕ}
    (V Ω : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin M) → ℝ)) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    referenceFrameCost V Ω hV hΩ v = bosonCutCost
      (covarianceHermitianOfForm (Pi.basisFun ℝ (Fin a ⊕ Fin M)) V hV)
      (commutatorHermitianOfForm (Pi.basisFun ℝ (Fin a ⊕ Fin M)) Ω hΩ) v := by
  unfold referenceFrameCost bosonFormCost referenceFrameCovariance bosonCutCost
  rw [covarianceHermitianOfForm_pullback (Pi.basisFun ℝ (Fin a ⊕ Fin M))
      (Pi.basisFun ℝ (Fin a ⊕ Fin k)) V hV (referenceFrameEmbedding v),
    commutatorHermitianOfForm_pullback (Pi.basisFun ℝ (Fin a ⊕ Fin M))
      (Pi.basisFun ℝ (Fin a ⊕ Fin k)) Ω hΩ (referenceFrameEmbedding v),
    referenceFrameEmbedding_matrix]

/-- True form nondegeneracy is exactly the determinant locus used by the
compact-sublevel theorem, even though forms may degenerate elsewhere. -/
theorem referenceFrame_nondegenerate_iff {a k M : ℕ}
    (Ω : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin M) → ℝ)) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    (referenceFrameCovariance Ω v).Nondegenerate ↔
      ((commutatorHermitianOfForm (Pi.basisFun ℝ (Fin a ⊕ Fin M)) Ω hΩ).conj
        (cutEmbedding (a := a) v)).mat.det ≠ 0 := by
  rw [← commutatorHermitianOfForm_det_ne_zero_iff (Pi.basisFun ℝ (Fin a ⊕ Fin k))
    (referenceFrameCovariance Ω v) (fun x => hΩ (referenceFrameEmbedding v x))]
  unfold referenceFrameCovariance
  rw [commutatorHermitianOfForm_pullback (Pi.basisFun ℝ (Fin a ⊕ Fin M))
    (Pi.basisFun ℝ (Fin a ⊕ Fin k)) Ω hΩ (referenceFrameEmbedding v),referenceFrameEmbedding_matrix]

/-- Actual minimum of the raw two-form objective on all admissible real
auxiliary frames of this size, without a global squeezing bound. -/
theorem exists_referenceFrameCost_minimum {a k M : ℕ}
    (V Ω : LinearMap.BilinForm ℝ ((Fin a ⊕ Fin M) → ℝ)) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (hpos : ∀ x, x≠0 → 0<V x x)
    (v₀ : Fin k → EuclideanSpace ℝ (Fin M)) (hv₀ : Orthonormal ℝ v₀)
    (hnd₀ : (referenceFrameCovariance Ω v₀).Nondegenerate) :
    ∃ v : Fin k → EuclideanSpace ℝ (Fin M), Orthonormal ℝ v ∧
      (referenceFrameCovariance Ω v).Nondegenerate ∧
      ∀ w : Fin k → EuclideanSpace ℝ (Fin M), Orthonormal ℝ w → (referenceFrameCovariance Ω w).Nondegenerate →
        referenceFrameCost V Ω hV hΩ v ≤ referenceFrameCost V Ω hV hΩ w := by
  obtain ⟨v,hv,hnd,hmin⟩ := exists_boson_cut_minimum
    (covarianceHermitianOfForm (Pi.basisFun ℝ (Fin a ⊕ Fin M)) V hV)
    (commutatorHermitianOfForm (Pi.basisFun ℝ (Fin a ⊕ Fin M)) Ω hΩ)
    (covarianceHermitianOfForm_posDef (Pi.basisFun ℝ (Fin a ⊕ Fin M)) V hV hpos) v₀ hv₀
    ((referenceFrame_nondegenerate_iff Ω hΩ v₀).mp hnd₀)
  refine ⟨v,hv,(referenceFrame_nondegenerate_iff Ω hΩ v).mpr hnd,?_⟩
  intro w hw hndw
  rw [referenceFrameCost_eq,referenceFrameCost_eq]
  exact hmin w hw ((referenceFrame_nondegenerate_iff Ω hΩ w).mp hndw)

end Gaussian.Phase
