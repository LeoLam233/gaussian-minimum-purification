import Gaussian.Phase.BosonicPurificationCost

/-! Equality transport for the actual two-form cost, including its symmetry
and alternation certificates. This avoids any dependent-rewrite assumptions. -/
noncomputable section
namespace Gaussian.Phase
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bosonFormCost_congr_forms (e : Module.Basis ι ℝ E)
    {V₁ V₂ Ω₁ Ω₂ : LinearMap.BilinForm ℝ E}
    (hV₁ : V₁.IsSymm) (hV₂ : V₂.IsSymm) (hΩ₁ : Ω₁.IsAlt) (hΩ₂ : Ω₂.IsAlt)
    (hV : V₁=V₂) (hΩ : Ω₁=Ω₂) :
    bosonFormCost e V₁ Ω₁ hV₁ hΩ₁ = bosonFormCost e V₂ Ω₂ hV₂ hΩ₂ := by
  subst V₂
  subst Ω₂
  rfl

end Gaussian.Phase
