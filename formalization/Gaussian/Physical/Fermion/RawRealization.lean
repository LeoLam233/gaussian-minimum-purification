import Gaussian.Physical.Fermion.OrthogonalSpectrum

/-! Realization of arbitrary raw finite skew contractions as actual CAR Wick
density states, rather than a realizability premise attached to covariance data. -/
noncomputable section
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- A paired eigenframe intertwines an arbitrary raw skew generator with the
explicit canonical thermal generator. -/
theorem pairedSkew_intertwine {n : ℕ}
    (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n)
    {J : OrthogonalComplexStructure (CoefficientSpace n)}
    {K : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n}
    (b : PairedEigenframe J K n) (hT : ∀ x,T x=J (K x))
    (ht : ∀ i,b.value i ∈ Set.Icc (-1:ℝ) 1) (v : CoefficientSpace n) :
    T (frameRotation b v) = frameRotation b (covarianceGenerator (thermal n b.value ht) v) := by
  have hL : T.comp (frameRotation b).toLinearEquiv.toLinearMap =
      (frameRotation b).toLinearEquiv.toLinearMap.comp (covarianceGenerator (thermal n b.value ht)) := by
    apply (EuclideanSpace.basisFun (MajoranaIndex n) ℝ).toBasis.ext
    intro a
    simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    change T (frameRotation b (coefficientBasis n a)) =
      frameRotation b (covarianceGenerator (thermal n b.value ht) (coefficientBasis n a))
    rcases a with ⟨i,k⟩
    cases k
    · rw [frameRotation_basis,boolFrame_false,hT,b.eigen,J.apply_smul,b.partner,
        thermalGenerator_false,map_smul,frameRotation_basis,boolFrame_true]
    · rw [frameRotation_basis,boolFrame_true,hT,b.eigen,J.apply_smul,b.partner_second,
        thermalGenerator_true,map_smul,frameRotation_basis,boolFrame_false]
      simp
  exact congrArg (fun L : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n => L v) hL

/-- Raw admissibility gives an explicitly constructed thermal orthogonal model,
including arbitrary kernel and repeated singular values. -/
theorem exists_raw_skew_thermal_model (n : ℕ)
    (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n) (hT : IsSkew T)
    (hBound : ∀ x,‖T x‖≤‖x‖) :
    ∃ (t : Fin n → ℝ) (ht : ∀ i,t i ∈ Set.Icc (-1:ℝ) 1)
      (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n),
      (∀ i,0≤t i) ∧ ∀ v,T (R v)=R (covarianceGenerator (thermal n t ht) v) := by
  have hd : finrank ℝ (CoefficientSpace n)=2*n := by
    simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
  obtain ⟨d⟩ := exists_skewAdaptation T hT (show Even (finrank ℝ (CoefficientSpace n)) from ⟨n,by omega⟩)
  obtain ⟨b⟩ := exists_pairedEigenframe_dim n (CoefficientSpace n) hd
    d.complexStructure d.K d.positive.isSymmetric d.commute
  have hlo (i : Fin n) : 0≤b.value i := by
    apply b.value_ge 0
    intro x
    simpa only [zero_mul] using d.positive.inner_nonneg_right x
  have hhi (i : Fin n) : b.value i≤1 := by
    have h := (d.one_sub_positive hBound).inner_nonneg_left (b.basis (i,0))
    change 0≤⟪b.basis (i,0)-d.K (b.basis (i,0)),b.basis (i,0)⟫ at h
    rw [b.eigen,inner_sub_left,real_inner_smul_left,b.basis.inner_eq_ite] at h
    simpa using h
  let ht : ∀ i,b.value i ∈ Set.Icc (-1:ℝ) 1 := fun i => ⟨by linarith [hlo i],hhi i⟩
  exact ⟨b.value,ht,frameRotation b,hlo,pairedSkew_intertwine T b d.factor ht⟩

/-- Every finite raw skew contraction is realized by an actual parity-invariant
quasifree density on the full 2^n occupation space. -/
theorem realize_skew_contraction (n : ℕ)
    (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n) (hT : IsSkew T)
    (hBound : ∀ x,‖T x‖≤‖x‖) :
    ∃ ρ : Density n,IsQuasifree ρ ∧ covarianceGenerator ρ=T := by
  obtain ⟨t,ht,R,hpos,hModel⟩ := exists_raw_skew_thermal_model n T hT hBound
  obtain ⟨U,hU⟩ := orthogonal_implemented n R
  refine ⟨(thermal n t ht).uConj U,rotated_thermal_isQuasifree n t ht R U hU,?_⟩
  apply LinearMap.ext
  intro v
  have h := (implemented_generator_intertwine (thermal n t ht) R U hU (R.symm v)).trans
    (hModel (R.symm v)).symm
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-- Equality of actual left-slot generators determines raw Wick density states. -/
theorem quasifree_eq_of_generator {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (hT : covarianceGenerator ρ=covarianceGenerator σ) : ρ=σ := by
  apply quasifree_eq_of_covariance ρ σ hρ hσ
  intro a b
  rw [← covarianceForm_basis,← covarianceForm_basis,← covarianceGenerator_inner,
    ← covarianceGenerator_inner,hT]

end Gaussian.Physical.Fermion
