import Gaussian.Phase.BosonicPurificationCore

/-! The opposite-commutator reference purifier from an actual paired eigenframe.
Both the symplectic Gram factor and the physical covariance restriction are proved. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section InnerGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric operator commuting with J is self-adjoint for Ω_J as well. -/
theorem symplectic_selfadjoint_of_symmetric_commute (J : OrthogonalComplexStructure E)
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hJ : ∀ x, J (T x) = T (J x)) (x y : E) :
    J.symplecticForm (T x) y = J.symplecticForm x (T y) := by
  change -⟪T x,J y⟫ = -⟪x,J (T y)⟫
  rw [hT,← hJ]

end InnerGeometry
section RawSqueezing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The proved hyperbolic block is symplectic for Ω⊕(-Ω), without invertibility
of either mixed block or any division by a squeezing parameter. -/
theorem squeezingEquiv_preserves_opposite (Ω : LinearMap.BilinForm ℝ E)
    (C S : E →ₗ[ℝ] E) (hcomm : ∀ x, C (S x) = S (C x))
    (hsq : ∀ x, C (C x)-S (S x)=x)
    (hC : ∀ x y, Ω (C x) y = Ω x (C y))
    (hS : ∀ x y, Ω (S x) y = Ω x (S y)) (x y : E × E) :
    doubledForm Ω (-Ω) (squeezingEquiv C S hcomm hsq x)
      (squeezingEquiv C S hcomm hsq y) = doubledForm Ω (-Ω) x y := by
  have h₁ := congrArg (fun z => Ω x.1 z) (hsq y.1)
  have h₂ := congrArg (fun z => Ω x.2 z) (hsq y.2)
  simp only [map_sub] at h₁ h₂
  simp only [doubledForm_apply,squeezingEquiv_apply,LinearMap.neg_apply,
    map_add,LinearMap.add_apply,hC,hS,hcomm]
  linarith

end RawSqueezing
section PureConstruction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pull back the positive vacuum Gram form by the explicitly symplectic
squeezing equivalence, obtaining an actual pure compatible covariance. -/
def pureOppositeOfFactors (J : OrthogonalComplexStructure E) (C S : E →ₗ[ℝ] E)
    (hCs : C.IsSymmetric) (hSs : S.IsSymmetric)
    (hJC : ∀ x, J (C x) = C (J x)) (hJS : ∀ x, J (S x) = S (J x))
    (hcomm : ∀ x, C (S x) = S (C x)) (hsq : ∀ x, C (C x)-S (S x)=x) :
    PureCompatibleCovariance (doubledForm J.symplecticForm (-J.symplecticForm)) :=
  ((basePureDouble J).pullback (squeezingEquiv C S hcomm hsq)).of_form_eq (by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact squeezingEquiv_preserves_opposite J.symplecticForm C S hcomm hsq
      (symplectic_selfadjoint_of_symmetric_commute J C hCs hJC)
      (symplectic_selfadjoint_of_symmetric_commute J S hSs hJS) x y)

/-- The physical block is the genuine sum of the two Gram blocks. -/
theorem pureOppositeOfFactors_physical (J : OrthogonalComplexStructure E)
    (C S : E →ₗ[ℝ] E) (hCs : C.IsSymmetric) (hSs : S.IsSymmetric)
    (hJC : ∀ x, J (C x) = C (J x)) (hJS : ∀ x, J (S x) = S (J x))
    (hcomm : ∀ x, C (S x) = S (C x)) (hsq : ∀ x, C (C x)-S (S x)=x) (x y : E) :
    (pureOppositeOfFactors J C S hCs hSs hJC hJS hcomm hsq).form (x,0) (y,0) =
      ⟪C x,C y⟫ + ⟪S x,S y⟫ := by
  simp [pureOppositeOfFactors,PureCompatibleCovariance.of_form_eq_form,
    PureCompatibleCovariance.pullback_form,basePureDouble]

end PureConstruction
namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- The actual reference purifier obtained from the constructed Williamson
parameters and frame. Pure endpoints and repeated parameters are retained. -/
def pureOpposite (hν : ∀ i, 1 ≤ b.value i) :
    PureCompatibleCovariance (doubledForm J.symplecticForm (-J.symplecticForm)) :=
  pureOppositeOfFactors J
    (b.modeDiagonal (fun i => purificationCosh (b.value i)))
    (b.modeDiagonal (fun i => purificationSinh (b.value i)))
    (b.modeDiagonal_symmetric _) (b.modeDiagonal_symmetric _)
    (b.modeDiagonal_commute_complex _) (b.modeDiagonal_commute_complex _)
    (b.modeDiagonal_commute _ _)
    (b.modeDiagonal_squares_sub _ _ (fun i => purification_factor_difference (hν i)))

/-- The constructed doubled pure covariance restricts to the original
amplitude covariance, rather than merely sharing its spectral list. -/
theorem pureOpposite_physical (hν : ∀ i, 1 ≤ b.value i) (x y : E) :
    (b.pureOpposite hν).form (x,0) (y,0) = ⟪x,K y⟫ := by
  unfold pureOpposite
  rw [pureOppositeOfFactors_physical,b.modeDiagonal_symmetric,b.modeDiagonal_symmetric,
    ← inner_add_right]
  congr 1
  exact b.modeDiagonal_squares_add _ _ (fun i => purification_factor_sum (hν i)) y

end PairedEigenframe
end Gaussian.Phase
