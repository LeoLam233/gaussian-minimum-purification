import Gaussian.Physical.Boson.WeylSymplectic
import Gaussian.Physical.Boson.MeanRemoval
import Gaussian.Analysis.ComplexGramProfile
import Gaussian.Covariance.Uncertainty

/-! Actual Gaussian Weyl states satisfy the raw covariance uncertainty inequality.
The proof uses bounded observable positivity and an exact one-sided derivative,
not an assumed unbounded-operator covariance bridge. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory Gaussian.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem centered_gaussian_gram_nonneg {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E×E)} (h : IsGaussianWith ρ 0 V) (z w : E×E) :
    0≤gramProfile (V z z) (V w w) (weylSymplecticForm E z w) (V (w-z) (w-z)) 1 := by
  have hd : V (z-w) (z-w)=V (w-z) (w-z) := by
    have he : z-w= -(w-z) := by abel
    rw [he]
    simp
    ring
  have huv := centered_expect_star_weyl_mul h z w
  have hvu : ρ.expect (star (weylOperator w.1 w.2 : Schrodinger E →L[ℂ] Schrodinger E)*
      (weylOperator z.1 z.2 : Schrodinger E →L[ℂ] Schrodinger E)) =
      Complex.exp (-(V (w-z) (w-z):ℂ)/4+(weylSymplecticForm E z w:ℂ)/2*Complex.I) := by
    rw [centered_expect_star_weyl_mul h w z,hd,weylSymplecticForm_swap w z]
    congr 1
    push_cast
    ring
  have hp := ρ.incrementGram_nonneg (weylOperator z.1 z.2) (weylOperator w.1 w.2)
  rw [centered_expect_weyl h z,centered_expect_star_weyl h z,
    centered_expect_weyl h w,centered_expect_star_weyl h w,huv,hvu] at hp
  change 0≤(complexGramScalar (V z z) (V w w) (weylSymplecticForm E z w) (V (w-z) (w-z))).re at hp
  rwa [complexGramScalar_re] at hp

theorem centered_gaussian_uncertainty {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E×E)} (h : IsGaussianWith ρ 0 V) :
    Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E) := by
  have hplus (z w : E×E) : 0≤V z z+V w w+2*weylSymplecticForm E z w := by
    apply gaussian_gram_coefficient_nonneg _ _ _ (V (w-z) (w-z))
    intro t
    have ht := centered_gaussian_gram_nonneg h (t • z) (t • w)
    simp only [← smul_sub,map_smul,LinearMap.smul_apply,smul_eq_mul] at ht
    rwa [gramProfile_scale] at ht
  intro z w
  have hp := hplus z (-w)
  simpa only [map_neg,LinearMap.neg_apply,neg_neg,mul_neg,← sub_eq_add_neg] using hp

/-- Physical normal Gaussianity itself supplies covariance uncertainty; no
positivity, full-rank or bounded-squeezing premise is added to the state domain. -/
theorem IsGaussianWith.uncertainty {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (h : IsGaussianWith ρ m V) :
    Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E) := by
  obtain ⟨a,b,hc,he⟩ := h.exists_centered_displacement
  exact centered_gaussian_uncertainty hc

theorem IsGaussianWith.covariance_pos {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (h : IsGaussianWith ρ m V) {z : E×E} (hz : z≠0) : 0<V z z :=
  Gaussian.Covariance.covariance_pos_of_nondegenerate h.uncertainty
    weylSymplecticForm_nondegenerate hz

end Gaussian.Physical.Boson
