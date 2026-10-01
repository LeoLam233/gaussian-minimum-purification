import Gaussian.Spectral.BosonicCanonical
import Gaussian.Phase.Williamson
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The proved raw Williamson basis supplies both complex congruences used by
the independently defined Hermitian-pair spectrum. -/
noncomputable section
open Module
open scoped Matrix ComplexOrder
namespace Gaussian.Spectral

@[simp] theorem complexifyMatrix_conjTranspose {m n : Type*} (A : Matrix m n ℝ) :
    (complexifyMatrix A).conjTranspose = complexifyMatrix A.transpose := by
  ext i j
  simp [complexifyMatrix, Matrix.conjTranspose_apply, Complex.star_def]

variable {E d : Type*} [AddCommGroup E] [Module ℝ E] [Fintype d] [DecidableEq d]

lemma complex_basis_congruence (e b : Basis d ℝ E) (V : LinearMap.BilinForm ℝ E) :
    (complexifyMatrix (e.toMatrix b)).conjTranspose * complexifyMatrix (V.toMatrix e) *
      complexifyMatrix (e.toMatrix b) = complexifyMatrix (V.toMatrix b) := by
  rw [complexifyMatrix_conjTranspose, ← complexifyMatrix_mul, ← complexifyMatrix_mul,
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix]

lemma complex_basis_det_isUnit (e b : Basis d ℝ E) :
    IsUnit (complexifyMatrix (e.toMatrix b)).det := by
  have h1 : complexifyMatrix (e.toMatrix b) * complexifyMatrix (b.toMatrix e) = 1 := by
    rw [← complexifyMatrix_mul, Basis.toMatrix_mul_toMatrix_flip, complexifyMatrix_one]
  have h2 : complexifyMatrix (b.toMatrix e) * complexifyMatrix (e.toMatrix b) = 1 := by
    rw [← complexifyMatrix_mul, Basis.toMatrix_mul_toMatrix_flip, complexifyMatrix_one]
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact ⟨⟨_,_,h1,h2⟩,rfl⟩

theorem exists_williamson_basis_bool [FiniteDimensional ℝ E]
    (V Ω : LinearMap.BilinForm ℝ E) (hVs : V.IsSymm)
    (hVp : ∀ x, x ≠ 0 → 0 < V x x) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    {n : ℕ} (hn : finrank ℝ E = 2*n)
    (hUnc : ∀ x y, (Ω x y)^2 ≤ V x x * V y y) :
    ∃ (ν : Fin n → ℝ) (b : Basis (Fin n × Bool) ℝ E),
      (∀ i,1 ≤ ν i) ∧
      (∀ i j, Ω (b i) (b j) = canonicalModeSkew n i j) ∧
      (∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0) := by
  obtain ⟨ν,b,hν,hΩ,hV⟩ := Gaussian.Phase.exists_williamson_basis V Ω hVs hVp hΩa hΩn hn hUnc
  let e : (Fin n × Fin 2) ≃ (Fin n × Bool) := Equiv.prodCongr (Equiv.refl _) finTwoEquiv
  refine ⟨ν,b.reindex e,hν,?_,?_⟩
  · rintro ⟨i,a⟩ ⟨j,c⟩
    simp only [Basis.reindex_apply,hΩ]
    cases a <;> cases c <;> simp [e,finTwoEquiv,Gaussian.Phase.canonicalModeMatrix,canonicalModeSkew]
  · intro i j
    simp only [Basis.reindex_apply,hV]
    by_cases h : i=j
    · subst j; simp [e]
    · have hh : e.symm i ≠ e.symm j := fun hij => h (e.symm.injective hij)
      simp only [hh,ite_false,h]

theorem exists_williamson_complex_congruences [FiniteDimensional ℝ E]
    (V Ω : LinearMap.BilinForm ℝ E) (hVs : V.IsSymm)
    (hVp : ∀ x, x ≠ 0 → 0 < V x x) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    {n : ℕ} (hn : finrank ℝ E = 2*n) (e : Basis (Fin n × Bool) ℝ E)
    (hUnc : ∀ x y, (Ω x y)^2 ≤ V x x * V y y) :
    ∃ (ν : Fin n → ℝ) (B : Matrix (Fin n × Bool) (Fin n × Bool) ℂ),
      (∀ i,1 ≤ ν i) ∧ IsUnit B.det ∧
      B.conjTranspose * complexifyMatrix (V.toMatrix e) * B = pairedDiagonal n ν ∧
      B.conjTranspose * (Complex.I • complexifyMatrix (Ω.toMatrix e)) * B = canonicalModeHermitian n := by
  obtain ⟨ν,b,hν,hΩ,hV⟩ := exists_williamson_basis_bool V Ω hVs hVp hΩa hΩn hn hUnc
  refine ⟨ν,complexifyMatrix (e.toMatrix b),hν,complex_basis_det_isUnit e b,?_,?_⟩
  · rw [complex_basis_congruence]
    ext i j
    simp only [complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,hV,pairedDiagonal,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  · rw [Matrix.mul_smul, Matrix.smul_mul, complex_basis_congruence]
    congr 1
    ext i j
    simp only [complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,hΩ]

/-- The coordinate covariance of a real symmetric form is independently Hermitian. -/
def covarianceHermitianOfForm (e : Basis d ℝ E) (V : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) : HermitianMat d ℂ :=
  ⟨complexifyMatrix (V.toMatrix e), by
    change (complexifyMatrix (V.toMatrix e)).conjTranspose = _
    rw [complexifyMatrix_conjTranspose, (V.isSymm_toMatrix_iff_isSymm e).mpr hV]⟩

/-- The coordinate iOmega of an alternating real form is independently Hermitian. -/
def commutatorHermitianOfForm (e : Basis d ℝ E) (Ω : LinearMap.BilinForm ℝ E)
    (hΩ : Ω.IsAlt) : HermitianMat d ℂ :=
  ⟨Complex.I • complexifyMatrix (Ω.toMatrix e), by
    change (Complex.I • complexifyMatrix (Ω.toMatrix e)).conjTranspose = _
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      complexifyMatrix, LinearMap.BilinForm.toMatrix_apply]
    rw [← hΩ.neg_eq (e i) (e j)]
    simp⟩

/-- Raw finite uncertainty data, in any fixed coefficient basis, produces the
actual Hermitian-pair entropy formula with constructed Williamson parameters.
No physical density realization or von Neumann entropy bridge is asserted here. -/
theorem exists_bosonPairCost_williamson [FiniteDimensional ℝ E]
    (V Ω : LinearMap.BilinForm ℝ E) (hVs : V.IsSymm)
    (hVp : ∀ x, x ≠ 0 → 0 < V x x) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    {n : ℕ} (hn : finrank ℝ E = 2*n) (e : Basis (Fin n × Bool) ℝ E)
    (hUnc : ∀ x y, (Ω x y)^2 ≤ V x x * V y y) :
    ∃ ν : Fin n → ℝ, (∀ i,1 ≤ ν i) ∧
      Gaussian.Attainment.bosonPairCost (covarianceHermitianOfForm e V hVs)
        (commutatorHermitianOfForm e Ω hΩa) = ∑ i, Gaussian.Entropy.boson (ν i) := by
  obtain ⟨ν,B,hν,hB,hD,hO⟩ := exists_williamson_complex_congruences V Ω hVs hVp hΩa hΩn hn e hUnc
  have hd : (pairedDiagonal n ν).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (hν i.1)
  have hcong : (B.conjTranspose * complexifyMatrix (V.toMatrix e) * B).PosDef := hD ▸ hd
  have hvh : (covarianceHermitianOfForm e V hVs).mat.PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff ((Matrix.isUnit_iff_isUnit_det B).mpr hB)).mp hcong
  refine ⟨ν,hν,?_⟩
  exact bosonPairCost_eq_sum_canonical _ _ hvh B hB ν
    (fun i => le_trans (by norm_num) (hν i)) hO hD

end Gaussian.Spectral
