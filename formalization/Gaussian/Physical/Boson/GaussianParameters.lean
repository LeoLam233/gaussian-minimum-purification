import Gaussian.Physical.Boson.GaussianPredicate
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! Uniqueness of the finite Gaussian characteristic parameters. This does not
assert density uniqueness from a characteristic function or moment realization. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem IsGaussianWith.covariance_unique {ρ : NormalDensity (Schrodinger E)}
    {m₁ m₂ : (E×E) →ₗ[ℝ] ℝ} {V₁ V₂ : LinearMap.BilinForm ℝ (E×E)}
    (h₁ : IsGaussianWith ρ m₁ V₁) (h₂ : IsGaussianWith ρ m₂ V₂) : V₁=V₂ := by
  apply LinearMap.BilinForm.ext_of_isSymm h₁.1 h₂.1
  intro z
  have he := congrArg norm ((h₁.2 z.1 z.2).symm.trans (h₂.2 z.1 z.2))
  rw [Complex.norm_exp,Complex.norm_exp] at he
  have hr : -(V₁ z z)/4=-(V₂ z z)/4 := by
    apply Real.exp_injective
    simpa using he
  linarith

theorem IsGaussianWith.mean_unique {ρ : NormalDensity (Schrodinger E)}
    {m₁ m₂ : (E×E) →ₗ[ℝ] ℝ} {V₁ V₂ : LinearMap.BilinForm ℝ (E×E)}
    (h₁ : IsGaussianWith ρ m₁ V₁) (h₂ : IsGaussianWith ρ m₂ V₂) : m₁=m₂ := by
  have hV := h₁.covariance_unique h₂
  subst V₂
  have hex (z : E×E) : Complex.exp (((m₁ z-m₂ z:ℝ):ℂ)*Complex.I)=1 := by
    have hh := (h₁.2 z.1 z.2).symm.trans (h₂.2 z.1 z.2)
    have hm : Complex.exp ((m₁ z:ℂ)*Complex.I)=Complex.exp ((m₂ z:ℂ)*Complex.I) := by
      apply (div_left_inj' (Complex.exp_ne_zero ((V₁ z z:ℂ)/4))).mp
      simpa only [Complex.exp_sub] using hh
    rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub,hm,div_self (Complex.exp_ne_zero _)]
  apply LinearMap.ext
  intro z
  by_contra hn
  have hd : m₁ z-m₂ z≠0 := sub_ne_zero.mpr hn
  let r : ℝ := Real.pi/(m₁ z-m₂ z)
  have hπ : m₁ (r • z)-m₂ (r • z)=Real.pi := by
    simp only [map_smul,smul_eq_mul]
    rw [← mul_sub]
    exact div_mul_cancel₀ Real.pi hd
  have hh := hex (r • z)
  rw [hπ,Complex.exp_pi_mul_I] at hh
  norm_num at hh

/-- Both characteristic parameters are unique once covariance symmetry is
part of the raw predicate. No state-realization or density-uniqueness premise is used. -/
theorem IsGaussianWith.parameters_unique {ρ : NormalDensity (Schrodinger E)}
    {m₁ m₂ : (E×E) →ₗ[ℝ] ℝ} {V₁ V₂ : LinearMap.BilinForm ℝ (E×E)}
    (h₁ : IsGaussianWith ρ m₁ V₁) (h₂ : IsGaussianWith ρ m₂ V₂) : m₁=m₂ ∧ V₁=V₂ :=
  ⟨h₁.mean_unique h₂,h₁.covariance_unique h₂⟩

end Gaussian.Physical.Boson
