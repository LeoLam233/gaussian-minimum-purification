import Gaussian.Spectral.WilliamsonCoefficients
import Gaussian.Entropy.Compression

/-! The independent Hermitian two-form covariance cost equals the adapted
amplitude half-spectrum, including actual restrictions of both original forms.
No density-state entropy is asserted or stored as an assumption. -/
noncomputable section
open Module Gaussian.Spectral
open scoped Matrix ComplexOrder RealInnerProductSpace
namespace Gaussian.Phase

section RawCost
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The independently defined Hermitian-pair cost of the original two forms
in a supplied coefficient basis. Admissibility is established by subsequent theorems. -/
def bosonFormCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ E) (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt) : ℝ :=
  Gaussian.Attainment.bosonPairCost (covarianceHermitianOfForm e V hV)
    (commutatorHermitianOfForm e Ω hΩ)

/-- Actual simultaneous canonical coefficients identify the independently
constructed Hermitian-pair cost with their once-per-mode sum. -/
theorem bosonFormCost_eq_canonical {n : ℕ}
    (e b : Basis (Fin n × Bool) ℝ E) (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩ : Ω.IsAlt) (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (hbV : ∀ i j, V (b i) (b j) = if i=j then ν i.1 else 0)
    (hbΩ : ∀ i j, Ω (b i) (b j) = canonicalModeSkew n i j) :
    bosonFormCost e V Ω hV hΩ = ∑ i, Gaussian.Entropy.boson (ν i) := by
  let B := complexifyMatrix (e.toMatrix b)
  have hB : IsUnit B.det := complex_basis_det_isUnit e b
  have hD : B.conjTranspose * complexifyMatrix (V.toMatrix e) * B = pairedDiagonal n ν := by
    dsimp only [B]
    rw [complex_basis_congruence]
    ext i j
    simp only [complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,hbV,pairedDiagonal,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  have hO : B.conjTranspose * (Complex.I • complexifyMatrix (Ω.toMatrix e)) * B =
      canonicalModeHermitian n := by
    dsimp only [B]
    rw [Matrix.mul_smul,Matrix.smul_mul,complex_basis_congruence]
    congr 1
    ext i j
    simp only [complexifyMatrix,LinearMap.BilinForm.toMatrix_apply,hbΩ]
  have hd : (pairedDiagonal n ν).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (hν i.1)
  have hc : (B.conjTranspose * complexifyMatrix (V.toMatrix e) * B).PosDef := hD ▸ hd
  have hpos : (covarianceHermitianOfForm e V hV).mat.PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff ((Matrix.isUnit_iff_isUnit_det B).mpr hB)).mp hc
  exact bosonPairCost_eq_sum_canonical _ _ hpos B hB ν
    (fun i => le_trans (by norm_num) (hν i)) hO hD

end RawCost

namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- Reindex the proved real paired basis by the canonical Boolean phase index. -/
def boolBasis : Basis (Fin n × Bool) ℝ E :=
  b.basis.toBasis.reindex (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)

/-- The coefficient cost uses both original forms and the genuine paired
frame, not a prescribed or assumed spectrum. -/
theorem formCost_eq_mode_sum (e : Basis (Fin n × Bool) ℝ E)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (hfactor : ∀ x y, V x y = ⟪x,K y⟫)
    (hcommutator : ∀ x y, Ω x y = J.symplecticForm x y)
    (hν : ∀ i, 1 ≤ b.value i) :
    bosonFormCost e V Ω hV hΩ = ∑ i, Gaussian.Entropy.boson (b.value i) := by
  apply bosonFormCost_eq_canonical e b.boolBasis V Ω hV hΩ b.value hν
  · intro i j
    simp only [boolBasis,Basis.reindex_apply,OrthonormalBasis.coe_toBasis,hfactor,b.amplitude_matrix]
    by_cases hij : i=j
    · subst j; simp
    · have hne : (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv).symm i ≠
          (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv).symm j := by
        intro he
        exact hij ((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv).symm.injective he)
      simp only [hne,ite_false,hij]
  · rintro ⟨i,a⟩ ⟨j,c⟩
    simp only [boolBasis,Basis.reindex_apply,OrthonormalBasis.coe_toBasis,hcommutator,b.symplectic_matrix]
    cases a <;> cases c <;> simp [finTwoEquiv,canonicalModeMatrix,canonicalModeSkew]

/-- Exact half-spectrum bridge for the independently defined two-form cost. -/
theorem formCost_eq_half_spectrum (e : Basis (Fin n × Bool) ℝ E)
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩ : Ω.IsAlt)
    (hfactor : ∀ x y, V x y = ⟪x,K y⟫)
    (hcommutator : ∀ x y, Ω x y = J.symplecticForm x y)
    (hν : ∀ i, 1 ≤ b.value i) (hK : K.IsSymmetric) (hn : finrank ℝ E = 2*n) :
    bosonFormCost e V Ω hV hΩ = Gaussian.Entropy.realListCost Gaussian.Entropy.boson
      (hK.eigenvalues hn) := by
  rw [b.formCost_eq_mode_sum e V Ω hV hΩ hfactor hcommutator hν]
  simpa only [Gaussian.Entropy.realListCost,one_div,div_eq_mul_inv,mul_comm,one_mul] using
    (paired_half_spectral_sum b hK Gaussian.Entropy.boson).symm

end PairedEigenframe
end Gaussian.Phase
