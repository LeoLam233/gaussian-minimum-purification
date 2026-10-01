import Gaussian.Phase.BosonicAdaptation
import Mathlib.Algebra.QuadraticDiscriminant

/-! The realification of the Hermitian uncertainty quadratic form.
No positivity of V is silently assumed: it is derived from uncertainty and
nondegeneracy of Ω. Actual state variance positivity remains a semantic bridge. -/
noncomputable section
namespace Gaussian.Covariance
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Positivity of V+iΩ on the complexified vector x+i y, written entirely in real forms.
The sign convention is immaterial for positivity because y ranges over all vectors. -/
def RealifiedUncertainty (V Ω : LinearMap.BilinForm ℝ E) : Prop :=
  ∀ x y, 0 ≤ V x x + V y y - 2 * Ω x y

theorem covariance_nonneg {V Ω : LinearMap.BilinForm ℝ E} (h : RealifiedUncertainty V Ω)
    (x : E) : 0 ≤ V x x := by simpa using h x 0

theorem robertson_inequality {V Ω : LinearMap.BilinForm ℝ E} (h : RealifiedUncertainty V Ω)
    (x y : E) : (Ω x y)^2 ≤ V x x * V y y := by
  have hq : ∀ t : ℝ, 0 ≤ V y y * (t*t) + (-2*Ω x y)*t + V x x := by
    intro t
    have ht := h x (t • y)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at ht
    nlinarith
  have hd := discrim_le_zero hq
  dsimp [discrim] at hd
  nlinarith

theorem realifiedUncertainty_iff (V Ω : LinearMap.BilinForm ℝ E) :
    RealifiedUncertainty V Ω ↔
      (∀ x, 0 ≤ V x x) ∧ (∀ x y, (Ω x y)^2 ≤ V x x * V y y) := by
  constructor
  · intro h; exact ⟨covariance_nonneg h,robertson_inequality h⟩
  · rintro ⟨hv,hr⟩ x y
    have hxy := hr x y
    have hx := hv x
    have hy := hv y
    nlinarith [sq_nonneg (V x x-V y y)]

/-- Finite bosonic covariance is positive definite as a consequence of uncertainty,
including the vacuous zero-mode case; this is not a full-rank assumption. -/
theorem covariance_pos_of_nondegenerate {V Ω : LinearMap.BilinForm ℝ E}
    (h : RealifiedUncertainty V Ω) (hΩ : Ω.Nondegenerate) {x : E} (hx : x ≠ 0) :
    0 < V x x := by
  apply lt_of_le_of_ne (covariance_nonneg h x)
  intro he
  apply hx
  apply hΩ.1
  intro y
  have hr := robertson_inequality h x y
  rw [← he,zero_mul] at hr
  nlinarith [sq_nonneg (Ω x y)]

theorem exists_bosonicAdaptation_from_uncertainty [FiniteDimensional ℝ E]
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hEven : Even (Module.finrank ℝ E)) (h : RealifiedUncertainty V Ω) :
    ∃ d : Gaussian.Phase.BosonicAdaptationData V Ω,
      ∀ x, d.g x x ≤ V x x := by
  exact Gaussian.Phase.exists_bosonicAdaptation V Ω hV
    (fun x hx => covariance_pos_of_nondegenerate h hΩn hx) hΩa hΩn hEven
    (robertson_inequality h)
end Gaussian.Covariance
