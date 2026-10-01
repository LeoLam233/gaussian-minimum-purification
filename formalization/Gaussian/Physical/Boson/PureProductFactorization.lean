import Gaussian.Physical.Boson.ProductDensity
import Gaussian.Physical.Boson.PartialTraceMatrix

/-! Actual pure-state/pure-marginal operator factorization on the full
Schrödinger product Hilbert space, without a Gaussian or covariance premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory Gaussian.Analysis
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def jointRightExtraction (f : Schrodinger E) :
    Schrodinger (JointConfiguration E F) →L[ℂ] Schrodinger F :=
  (jointProductEmbeddingLeft f).adjoint

theorem jointRightExtraction_inner (f : Schrodinger E) (g : Schrodinger F)
    (u : Schrodinger (JointConfiguration E F)) :
    ⟪g,jointRightExtraction f u⟫_ℂ=⟪jointProduct f g,u⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (jointProductEmbeddingLeft f) g u

theorem vectorDensity_jointProduct (x : Schrodinger E) (y : Schrodinger F)
    (hx : ‖x‖=1) (hy : ‖y‖=1) :
    vectorDensity (jointProduct x y) (by rw [jointProduct_norm,hx,hy,one_mul])=
      (vectorDensity x hx).product (vectorDensity y hy) := by
  apply NormalDensity.ext_characteristic
  intro q p
  rw [NormalDensity.characteristic_product]
  simp only [NormalDensity.characteristic,vectorDensity_expect,weylOperator_apply,
    weyl_jointProduct,jointProduct_inner]

theorem pure_leftReduction_extraction_norm
    (ψ : Schrodinger (JointConfiguration E F)) (hψ : ‖ψ‖=1)
    (x : Schrodinger E) (hx : ‖x‖=1)
    (hm : (vectorDensity ψ hψ).leftReduction=vectorDensity x hx) :
    ‖jointRightExtraction x ψ‖=1 := by
  let c := chosenHilbertBasis (Schrodinger F)
  let y := jointRightExtraction x ψ
  have ht := (vectorDensity ψ hψ).leftReduction_matrix_hasSum c x x
  rw [hm] at ht
  have he (j) : ⟪jointProduct x (c j),(vectorDensity ψ hψ).operator.1 (jointProduct x (c j))⟫_ℂ=
      ((‖⟪c j,y⟫_ℂ‖^2:ℝ):ℂ) := by
    change ⟪jointProduct x (c j),InnerProductSpace.rankOne ℂ ψ ψ (jointProduct x (c j))⟫_ℂ=_
    rw [InnerProductSpace.rankOne_apply,inner_smul_right]
    rw [← inner_conj_symm ψ (jointProduct x (c j)),Complex.conj_mul']
    rw [← jointRightExtraction_inner x (c j) ψ]
    simp only [y,Complex.ofReal_pow]
  have ht' : HasSum (fun j => ((‖⟪c j,y⟫_ℂ‖^2:ℝ):ℂ)) (1:ℂ) := by
    have htt := ht.congr_fun (fun j => (he j).symm)
    simpa [vectorDensity,vectorOperator_coe,InnerProductSpace.rankOne_apply,
      inner_smul_right,inner_self_eq_norm_sq_to_K,hx,Complex.ofReal_one,one_pow,one_mul] using htt
  have hn := Complex.hasSum_ofReal.mpr (hasSum_hilbert_coeff_norm_sq c y)
  have hsq : ‖y‖^2=1 := by
    have h : ((‖y‖^2:ℝ):ℂ)=1 := hn.unique ht'
    exact_mod_cast h
  have hy := norm_nonneg y
  change ‖y‖=1
  nlinarith

theorem pure_vector_eq_jointProduct_of_pure_leftReduction
    (ψ : Schrodinger (JointConfiguration E F)) (hψ : ‖ψ‖=1)
    (x : Schrodinger E) (hx : ‖x‖=1)
    (hm : (vectorDensity ψ hψ).leftReduction=vectorDensity x hx) :
    ψ=jointProduct x (jointRightExtraction x ψ) := by
  let y := jointRightExtraction x ψ
  have hy : ‖y‖=1 := pure_leftReduction_extraction_norm ψ hψ x hx hm
  have hi : ⟪ψ,jointProduct x y⟫_ℂ=1 := by
    rw [← inner_conj_symm ψ (jointProduct x y),← jointRightExtraction_inner x y ψ]
    change (starRingEnd ℂ) ⟪y,y⟫_ℂ=1
    simp [inner_self_eq_norm_sq_to_K,hy]
  have hz : ‖ψ-jointProduct x y‖^2=0 := by
    rw [norm_sub_sq (𝕜 := ℂ),hψ,jointProduct_norm,hx,hy,hi]
    norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- A genuine pure normal density with pure actual left marginal is a product
of that marginal with a genuine pure normal density on the environment. -/
theorem NormalDensity.IsPure.factor_of_pure_leftReduction
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    (hρ : ρ.IsPure) (hL : ρ.leftReduction.IsPure) :
    ∃ y : Schrodinger F,∃ hy : ‖y‖=1,ρ=ρ.leftReduction.product (vectorDensity y hy) := by
  obtain ⟨ψ,hψ,rfl⟩ := hρ
  obtain ⟨x,hx,hm⟩ := hL
  let y := jointRightExtraction x ψ
  have hy : ‖y‖=1 := pure_leftReduction_extraction_norm ψ hψ x hx hm
  refine ⟨y,hy,?_⟩
  rw [hm]
  have he := pure_vector_eq_jointProduct_of_pure_leftReduction ψ hψ x hx hm
  have hs : vectorDensity ψ hψ=vectorDensity (jointProduct x y)
      (by rw [jointProduct_norm,hx,hy,one_mul]) := by
    apply NormalDensity.ext
    exact congrArg vectorOperator he
  exact hs.trans (vectorDensity_jointProduct x y hx hy)

end Gaussian.Physical.Boson
