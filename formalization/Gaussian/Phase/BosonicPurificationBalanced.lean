import Gaussian.Phase.BosonicPurification

/-! Both diagonal covariances of the actual same-sign doubled reference are the
original V. The auxiliary orientation reflection is proved to preserve K,
including repeated eigenvalues and pure endpoints. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

section Factors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pureOppositeOfFactors_auxiliary (J : OrthogonalComplexStructure E)
    (C S : E →ₗ[ℝ] E) (hCs : C.IsSymmetric) (hSs : S.IsSymmetric)
    (hJC : ∀ x, J (C x) = C (J x)) (hJS : ∀ x, J (S x) = S (J x))
    (hcomm : ∀ x, C (S x) = S (C x)) (hsq : ∀ x, C (C x)-S (S x)=x) (x y : E) :
    (pureOppositeOfFactors J C S hCs hSs hJC hJS hcomm hsq).form (0,x) (0,y) =
      ⟪S x,S y⟫ + ⟪C x,C y⟫ := by
  simp [pureOppositeOfFactors,PureCompatibleCovariance.of_form_eq_form,
    PureCompatibleCovariance.pullback_form,basePureDouble]

end Factors
namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- The actual orientation reflection commutes with the actual amplitude. -/
theorem reflection_commute_amplitude (x : E) : K (b.reflection x) = b.reflection (K x) := by
  have h : K.comp b.reflectionMap = b.reflectionMap.comp K := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change K (b.reflectionMap (b.basis (i,k))) = b.reflectionMap (K (b.basis (i,k)))
    fin_cases k <;> simp [b.eigen]
  exact LinearMap.congr_fun h x

/-- The opposite-form Gram construction has the same actual diagonal on both copies. -/
theorem pureOpposite_auxiliary (hν : ∀ i, 1 ≤ b.value i) (x y : E) :
    (b.pureOpposite hν).form (0,x) (0,y) = ⟪x,K y⟫ := by
  unfold pureOpposite
  rw [pureOppositeOfFactors_auxiliary,b.modeDiagonal_symmetric,b.modeDiagonal_symmetric,
    ← inner_add_right]
  congr 1
  rw [add_comm]
  exact b.modeDiagonal_squares_add _ _ (fun i => purification_factor_sum (hν i)) y

/-- Reversing the auxiliary orientation preserves the actual auxiliary covariance. -/
theorem pureSame_auxiliary (hν : ∀ i, 1 ≤ b.value i) (x y : E) :
    (b.pureSame hν).form (0,x) (0,y) = ⟪x,K y⟫ := by
  simp only [pureSame,PureCompatibleCovariance.of_form_eq_form,
    PureCompatibleCovariance.pullback_form,auxiliaryOrientation_apply]
  rw [b.pureOpposite_auxiliary,b.reflection_commute_amplitude,b.reflection.inner_map_map]

end PairedEigenframe

/-- An explicit doubled same-sign pure reference with BOTH diagonal covariances
exactly equal to the original admissible covariance. -/
theorem exists_balanced_bosonic_reference
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) :
    ∃ p : PureCompatibleCovariance (doubledForm Ω Ω),
      (∀ x y, p.form (x,0) (y,0) = V x y) ∧
      (∀ x y, p.form (0,x) (0,y) = V x y) := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  obtain ⟨d,hLower⟩ := Gaussian.Covariance.exists_bosonicAdaptation_from_uncertainty
    V Ω hV hΩa hΩn ⟨n,hn⟩ hUnc
  letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
  have hn' : finrank ℝ E = 2*n := by omega
  let b := d.pairedFrame hn'
  have hν : ∀ i, 1 ≤ b.value i := d.pairedFrame_value_ge_one hLower hn'
  let q := b.pureSame hν
  have hΩ : doubledForm d.complexStructure.symplecticForm d.complexStructure.symplecticForm =
      doubledForm Ω Ω := by rw [d.complexStructure_symplecticForm]
  refine ⟨q.of_form_eq hΩ,?_,?_⟩
  · intro x y
    rw [PureCompatibleCovariance.of_form_eq_form]
    change (b.pureSame hν).form (x,0) (y,0) = V x y
    rw [b.pureSame_physical]
    exact (d.covariance_factor x y).symm
  · intro x y
    rw [PureCompatibleCovariance.of_form_eq_form]
    change (b.pureSame hν).form (0,x) (0,y) = V x y
    rw [b.pureSame_auxiliary]
    exact (d.covariance_factor x y).symm

end Gaussian.Phase
