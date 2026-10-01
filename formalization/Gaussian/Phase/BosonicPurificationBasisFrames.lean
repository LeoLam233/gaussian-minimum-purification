import Gaussian.Phase.BosonicPurificationFrameMinimum

/-! The compact real-frame minimum on arbitrary actual finite coefficient
spaces, with basis choices visible and literal physical/frame images proved. -/
noncomputable section
open Module Gaussian.Spectral Gaussian.Attainment
open scoped Matrix ComplexOrder
namespace Gaussian.Phase
variable {E D : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup D] [Module ℝ D] [FiniteDimensional ℝ D]
  {a k M : ℕ}

def basisReferenceFrameEmbedding (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D) (v : Fin k → EuclideanSpace ℝ (Fin M)) : D →ₗ[ℝ] E :=
  Matrix.toLin b e (realReferenceCutMatrix (a := a) v).transpose

theorem basisReferenceFrameEmbedding_matrix (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D) (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    (complexifyMatrix (LinearMap.toMatrix b e (basisReferenceFrameEmbedding e b v))).conjTranspose =
      cutEmbedding (a := a) v := by
  rw [basisReferenceFrameEmbedding,LinearMap.toMatrix_toLin]
  simpa only [referenceFrameEmbedding,LinearMap.toMatrix_toLin] using
    referenceFrameEmbedding_matrix (a := a) v

theorem basisReferenceFrameEmbedding_physical (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D) (v : Fin k → EuclideanSpace ℝ (Fin M)) (i : Fin a) :
    basisReferenceFrameEmbedding e b v (b (Sum.inl i)) = e (Sum.inl i) := by
  rw [basisReferenceFrameEmbedding,Matrix.toLin_self]
  simp [realReferenceCutMatrix,Matrix.transpose_apply,Fintype.sum_sum_type,Matrix.one_apply,Matrix.fromBlocks]

theorem basisReferenceFrameEmbedding_auxiliary (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D) (v : Fin k → EuclideanSpace ℝ (Fin M)) (i : Fin k) :
    basisReferenceFrameEmbedding e b v (b (Sum.inr i)) = ∑ j, (v i) j • e (Sum.inr j) := by
  rw [basisReferenceFrameEmbedding,Matrix.toLin_self]
  simp [realReferenceCutMatrix,Matrix.transpose_apply,Fintype.sum_sum_type,Matrix.fromBlocks]

def basisReferenceFrameCost (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) : ℝ :=
  bosonFormCost b
    (V.compl₁₂ (basisReferenceFrameEmbedding e b v) (basisReferenceFrameEmbedding e b v))
    (Ω.compl₁₂ (basisReferenceFrameEmbedding e b v) (basisReferenceFrameEmbedding e b v))
    ⟨fun x y => hV.eq (basisReferenceFrameEmbedding e b v x) (basisReferenceFrameEmbedding e b v y)⟩
    (fun x => hΩ (basisReferenceFrameEmbedding e b v x))

theorem basisReferenceFrameCost_eq (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    basisReferenceFrameCost e b V Ω hV hΩ v =
      bosonCutCost (covarianceHermitianOfForm e V hV) (commutatorHermitianOfForm e Ω hΩ) v := by
  unfold basisReferenceFrameCost bosonFormCost bosonCutCost
  rw [covarianceHermitianOfForm_pullback e b V hV (basisReferenceFrameEmbedding e b v),
    commutatorHermitianOfForm_pullback e b Ω hΩ (basisReferenceFrameEmbedding e b v),
    basisReferenceFrameEmbedding_matrix]

theorem basisReferenceFrame_nondegenerate_iff (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D) (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt)
    (v : Fin k → EuclideanSpace ℝ (Fin M)) :
    (Ω.compl₁₂ (basisReferenceFrameEmbedding e b v) (basisReferenceFrameEmbedding e b v)).Nondegenerate ↔
      ((commutatorHermitianOfForm e Ω hΩ).conj (cutEmbedding (a := a) v)).mat.det ≠ 0 := by
  change LinearMap.BilinForm.Nondegenerate (Ω.compl₁₂ (basisReferenceFrameEmbedding e b v)
    (basisReferenceFrameEmbedding e b v)) ↔ _
  rw [← commutatorHermitianOfForm_det_ne_zero_iff b _
    (fun x => hΩ (basisReferenceFrameEmbedding e b v x))]
  rw [commutatorHermitianOfForm_pullback e b Ω hΩ (basisReferenceFrameEmbedding e b v),
    basisReferenceFrameEmbedding_matrix]

/-- The actual fixed-reference covariance minimum over every admissible real
auxiliary frame, stated on arbitrary finite coefficient spaces. -/
theorem exists_basisReferenceFrameCost_minimum (e : Basis (Fin a ⊕ Fin M) ℝ E)
    (b : Basis (Fin a ⊕ Fin k) ℝ D)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (hpos : ∀ x, x≠0 → 0<V x x)
    (v₀ : Fin k → EuclideanSpace ℝ (Fin M)) (hv₀ : Orthonormal ℝ v₀)
    (hnd₀ : (Ω.compl₁₂ (basisReferenceFrameEmbedding e b v₀)
      (basisReferenceFrameEmbedding e b v₀)).Nondegenerate) :
    ∃ v : Fin k → EuclideanSpace ℝ (Fin M), Orthonormal ℝ v ∧
      (Ω.compl₁₂ (basisReferenceFrameEmbedding e b v) (basisReferenceFrameEmbedding e b v)).Nondegenerate ∧
      ∀ w : Fin k → EuclideanSpace ℝ (Fin M), Orthonormal ℝ w →
        (Ω.compl₁₂ (basisReferenceFrameEmbedding e b w) (basisReferenceFrameEmbedding e b w)).Nondegenerate →
        basisReferenceFrameCost e b V Ω hV hΩ v ≤ basisReferenceFrameCost e b V Ω hV hΩ w := by
  obtain ⟨v,hv,hnd,hmin⟩ := exists_boson_cut_minimum
    (covarianceHermitianOfForm e V hV) (commutatorHermitianOfForm e Ω hΩ)
    (covarianceHermitianOfForm_posDef e V hV hpos) v₀ hv₀
    ((basisReferenceFrame_nondegenerate_iff e b Ω hΩ v₀).mp hnd₀)
  refine ⟨v,hv,(basisReferenceFrame_nondegenerate_iff e b Ω hΩ v).mpr hnd,?_⟩
  intro w hw hndw
  rw [basisReferenceFrameCost_eq,basisReferenceFrameCost_eq]
  exact hmin w hw ((basisReferenceFrame_nondegenerate_iff e b Ω hΩ w).mp hndw)

end Gaussian.Phase
