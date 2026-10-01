import Gaussian.Attainment.InverseFactor

/-! Compact-sublevel attainment for continuous finite covariance/form pairs.
The commutator form is allowed to degenerate off the minimizing sublevel. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Gaussian.Attainment
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]

lemma matrixCLM_injective_iff_det_ne_zero (A : Matrix ι ι ℂ) :
    Function.Injective ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A) ↔ A.det ≠ 0 := by
  constructor
  · intro h
    have hs : Function.Surjective ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A) :=
      (LinearMap.injective_iff_surjective).mp h
    have hu := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨h,hs⟩
    have hA : IsUnit A := by
      simpa only [StarAlgEquiv.symm_apply_apply] using hu.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  · intro h
    have hA := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h)
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp (hA.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)))).1

lemma matrix_inverse_bound_lower (A : Matrix ι ι ℂ) (hA : A.det ≠ 0)
    {C : ℝ} (hC : 0 < C) (hInv : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A⁻¹‖ ≤ C)
    (x : EuclideanSpace ℂ ι) : C⁻¹ * ‖x‖ ≤ ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x‖ := by
  have hid : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A⁻¹ * (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), map_one]
  have hx := congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T x) hid
  have hn := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A⁻¹).le_opNorm ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x)
  change ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A⁻¹ * (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A) x‖ ≤ _ at hn
  rw [hid] at hn
  have h : ‖x‖ ≤ C * ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A x‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)

lemma continuous_matrixCLM : Continuous ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))) :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

lemma exists_inverse_sqrt_bound (F : Set X) (hF : IsCompact F)
    (V : X → HermitianMat ι ℂ) (hV : Continuous V)
    (hpos : ∀ p ∈ F, (V p).mat.PosDef) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ F, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (V p).sqrt.mat⁻¹‖ ≤ B := by
  have hs : Continuous (fun p => (V p).sqrt) :=
    (HermitianMat.cfc_continuous Real.continuous_sqrt).comp hV
  have hi : ContinuousOn (fun p => ((V p).sqrt⁻¹).mat) F :=
    HermitianMat.continuous_mat.comp_continuousOn
      (continuousOn_hermitian_inv.comp hs.continuousOn
        (fun p hp => (HermitianMat.sqrt_posDef (hpos p hp)).det_pos.ne'))
  have hn : ContinuousOn (fun p => ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (V p).sqrt.mat⁻¹‖) F :=
    (continuous_matrixCLM.comp_continuousOn hi).norm
  obtain ⟨B,hB⟩ := hF.bddAbove_image hn
  refine ⟨max B 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro p hp
  exact (hB ⟨p,hp,rfl⟩).trans (le_max_left _ _)

set_option maxHeartbeats 500000 in
/-- Exact attainment on every nonempty compact family of positive covariance pairs.
No global bound on inverse commutator or squeezing is assumed: the bound is
proved only on the finite objective sublevel of an arbitrary admissible point. -/
theorem exists_bosonPairCost_minimum (F : Set X) (hF : IsCompact F)
    (V O : X → HermitianMat ι ℂ) (hV : Continuous V) (hO : Continuous O)
    (hpos : ∀ p ∈ F, (V p).mat.PosDef)
    (p₀ : X) (hp₀ : p₀ ∈ F) (hO₀ : (O p₀).mat.det ≠ 0) :
    ∃ p ∈ F, (O p).mat.det ≠ 0 ∧
      ∀ q ∈ F, (O q).mat.det ≠ 0 → bosonPairCost (V p) (O p) ≤ bosonPairCost (V q) (O q) := by
  let T : X → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    fun p => Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (O p).mat
  have hT : Continuous T := continuous_matrixCLM.comp (HermitianMat.continuous_mat.comp hO)
  have hnd : ∀ p, p ∈ nondegenerateLocus T ↔ (O p).mat.det ≠ 0 :=
    fun p => matrixCLM_injective_iff_det_ne_zero (O p).mat
  let f : X → ℝ := fun p => bosonPairCost (V p) (O p)
  have hf : ContinuousOn f (F ∩ nondegenerateLocus T) := by
    have hc : ContinuousOn
        (fun z : HermitianMat ι ℂ × HermitianMat ι ℂ => bosonPairCost z.1 z.2)
        {z | z.2.mat.det ≠ 0} := continuousOn_bosonPairCost
    have hp : ContinuousOn (fun p => (V p, O p)) (F ∩ nondegenerateLocus T) :=
      (hV.prodMk hO).continuousOn
    have hm : Set.MapsTo (fun p => (V p, O p)) (F ∩ nondegenerateLocus T)
        {z | z.2.mat.det ≠ 0} := fun p hp => (hnd p).mp hp.2
    have hh := hc.comp hp hm
    dsimp only [Function.comp_def] at hh
    exact hh
  obtain ⟨B,hB,hBound⟩ := exists_inverse_sqrt_bound F hF V hV hpos
  obtain ⟨D,hD,hDmean⟩ := exists_bosonHermitianCost_operator_bound (ι := ι) (f p₀)
  let C := B^2*D
  have hC : 0 < C := mul_pos (sq_pos_of_pos hB) hD
  have hsub : ∀ p ∈ F ∩ nondegenerateLocus T, f p ≤ f p₀ → p ∈ lowerBoundLocus T C⁻¹ := by
    intro p hp hcost x
    have hInv : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (O p).mat⁻¹‖ ≤ C := by
      calc
        _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (V p).sqrt.mat⁻¹‖^2 *
            ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (bosonPairHermitian (V p) (O p)).mat‖ :=
          bosonPair_inverse_norm (V p) (O p) (hpos p hp.1)
        _ ≤ B^2*D := mul_le_mul
          ((sq_le_sq₀ (norm_nonneg _) hB.le).mpr (hBound p hp.1))
          (hDmean _ hcost) (norm_nonneg _) (sq_nonneg B)
    exact matrix_inverse_bound_lower (O p).mat ((hnd p).mp hp.2) hC hInv x
  obtain ⟨p,hp,hmin⟩ := exists_minimum_of_sublevel_lowerBound F hF T hT f hf
    p₀ ⟨hp₀,(hnd p₀).mpr hO₀⟩ C⁻¹ (inv_pos.mpr hC) hsub
  exact ⟨p,hp.1,(hnd p).mp hp.2,fun q hq hOq => hmin q ⟨hq,(hnd q).mpr hOq⟩⟩

end Gaussian.Attainment
