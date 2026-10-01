import Gaussian.Phase.BosonicPurificationCostTransport

/-! The covariance/form matrices of actual coefficient embeddings. Rectangular
compression transforms both forms, and its nondegenerate locus is exactly the
nondegeneracy of the genuinely pulled-back alternating form. -/
noncomputable section
open Module Gaussian.Spectral
open scoped Matrix ComplexOrder RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Strict positivity of a raw real symmetric covariance gives strict positivity
of its independently complexified Hermitian coefficient matrix. -/
theorem covarianceHermitianOfForm_posDef (e : Basis ι ℝ E)
    (V : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hpos : ∀ x, x≠0 → 0<V x x) : (covarianceHermitianOfForm e V hV).mat.PosDef := by
  let core := covarianceInnerCore V hV hpos
  letI : NormedAddCommGroup E := core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  let q : Fin (finrank ℝ E) ≃ ι := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis e)
  let b : Basis ι ℝ E := (stdOrthonormalBasis ℝ E).toBasis.reindex q
  have hId : complexifyMatrix (V.toMatrix b) = (1 : Matrix ι ι ℂ) := by
    ext i j
    simp only [complexifyMatrix,LinearMap.BilinForm.toMatrix_apply]
    change (((⟪b i,b j⟫ : ℝ)) : ℂ) = (1 : Matrix ι ι ℂ) i j
    simp only [b,Basis.reindex_apply,OrthonormalBasis.coe_toBasis,
      (stdOrthonormalBasis ℝ E).inner_eq_ite,q.symm.injective.eq_iff,Matrix.one_apply]
    split_ifs <;> simp
  let B := complexifyMatrix (e.toMatrix b)
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (complex_basis_det_isUnit e b)
  change (complexifyMatrix (V.toMatrix e)).PosDef
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff hB).mp
  change ((complexifyMatrix (e.toMatrix b)).conjTranspose * complexifyMatrix (V.toMatrix e) *
    complexifyMatrix (e.toMatrix b)).PosDef
  rw [complex_basis_congruence,hId]
  exact Matrix.PosDef.one

/-- The determinant condition used by compact attainment is exactly actual
alternating-form nondegeneracy, including dimension zero. -/
theorem commutatorHermitianOfForm_det_ne_zero_iff (e : Basis ι ℝ E)
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) :
    (commutatorHermitianOfForm e Ω hΩ).mat.det ≠ 0 ↔ Ω.Nondegenerate := by
  have hd : (complexifyMatrix (Ω.toMatrix e)).det = ((Ω.toMatrix e).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom (Ω.toMatrix e)).symm
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e]
  change (Complex.I • complexifyMatrix (Ω.toMatrix e)).det ≠ 0 ↔ _
  simp [Matrix.det_smul,hd]

/-- Actual simultaneous pullback is rectangular coefficient congruence. -/
theorem complex_form_pullback (e : Basis ι ℝ E) (b : Basis κ ℝ F)
    (V : LinearMap.BilinForm ℝ E) (f : F →ₗ[ℝ] E) :
    complexifyMatrix (LinearMap.BilinForm.toMatrix b (V.compl₁₂ f f)) =
      (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose *
        complexifyMatrix (V.toMatrix e) * complexifyMatrix (LinearMap.toMatrix b e f) := by
  rw [complexifyMatrix_conjTranspose,← complexifyMatrix_mul,← complexifyMatrix_mul]
  congr 1
  exact LinearMap.BilinForm.toMatrix_comp e b V f f

/-- The Hermitian covariance is the genuine rectangular matrix compression. -/
theorem covarianceHermitianOfForm_pullback (e : Basis ι ℝ E) (b : Basis κ ℝ F)
    (V : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (f : F →ₗ[ℝ] E) :
    covarianceHermitianOfForm b (V.compl₁₂ f f) ⟨fun x y => hV.eq (f x) (f y)⟩ =
      (covarianceHermitianOfForm e V hV).conj
        (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose := by
  apply HermitianMat.ext
  change complexifyMatrix (LinearMap.BilinForm.toMatrix b (V.compl₁₂ f f)) =
    (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose *
      complexifyMatrix (V.toMatrix e) *
      (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose]
  exact complex_form_pullback e b V f

/-- The commutator is compressed by the same actual rectangular map. -/
theorem commutatorHermitianOfForm_pullback (e : Basis ι ℝ E) (b : Basis κ ℝ F)
    (Ω : LinearMap.BilinForm ℝ E) (hΩ : Ω.IsAlt) (f : F →ₗ[ℝ] E) :
    commutatorHermitianOfForm b (Ω.compl₁₂ f f) (fun x => hΩ (f x)) =
      (commutatorHermitianOfForm e Ω hΩ).conj
        (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose := by
  apply HermitianMat.ext
  change Complex.I • complexifyMatrix (LinearMap.BilinForm.toMatrix b (Ω.compl₁₂ f f)) =
    (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose *
      (Complex.I • complexifyMatrix (Ω.toMatrix e)) *
      (complexifyMatrix (LinearMap.toMatrix b e f)).conjTranspose.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose,complex_form_pullback e b Ω f,Matrix.mul_smul,Matrix.smul_mul]

/-- Pullback through an injective coefficient embedding has precisely the cost
of the actual range restriction, independently of the chosen two bases. -/
theorem bosonFormCost_embedding (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩ : Ω.IsAlt) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (f : F →ₗ[ℝ] E) (hf : Function.Injective f) (hnd : (Ω.restrict f.range).Nondegenerate)
    (e : Basis ι ℝ F) (b : Basis κ ℝ f.range) :
    bosonFormCost e (V.compl₁₂ f f) (Ω.compl₁₂ f f)
      ⟨fun x y => hV.eq (f x) (f y)⟩ (fun x => hΩ (f x)) =
      bosonFormCost b (V.restrict f.range) (Ω.restrict f.range)
        (hV.restrict _) (fun x => hΩ x) := by
  exact bosonFormCost_pullback_general (V.restrict f.range) (Ω.restrict f.range)
    (hV.restrict _) (fun x => hΩ x) hnd (fun x y => hUnc x y)
    (LinearEquiv.ofInjective f hf) b e

end Gaussian.Phase
