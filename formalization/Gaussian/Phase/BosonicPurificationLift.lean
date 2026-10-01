import Gaussian.Phase.BosonicPurificationDelete

/-! A pure covariance on an actually embedded factor forces invariance under
the ambient pure generator. The factor may first have been found inside a
mixed cut; no invariance under the ambient generator is presumed. -/
noncomputable section
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

/-- Local pure covariance, when its two forms are the actual pullbacks, implies
ambient invariance of the embedded range. -/
theorem invariant_range_of_pure_embedding (d : PureCompatibleCovariance Ω)
    (p : PureCompatibleCovariance σ) (f : F →ₗ[ℝ] E) (hf : Function.Injective f)
    (hΩ : ∀ x y, Ω (f x) (f y) = σ x y)
    (hV : ∀ x y, d.form (f x) (f y) = p.form x y) :
    ∀ x ∈ f.range, d.generator x ∈ f.range := by
  let e : F ≃ₗ[ℝ] f.range := LinearEquiv.ofInjective f hf
  let Jp : f.range →ₗ[ℝ] f.range := e.conj p.generator
  have hsq : ∀ x, Jp (Jp x) = -x := by
    intro x
    simp [Jp,LinearEquiv.conj_apply,p.square_neg]
  apply d.pure_restriction_invariant f.range Jp hsq
  intro x y
  have hx : (x : E) = f (e.symm x) := (congrArg Subtype.val (e.apply_symm_apply x)).symm
  have hy : (y : E) = f (e.symm y) := (congrArg Subtype.val (e.apply_symm_apply y)).symm
  have hJy : (Jp y : E) = f (p.generator (e.symm y)) := rfl
  change d.form (x : E) (y : E) = Ω (x : E) (Jp y : E)
  rw [hx,hy,hJy,hV,hΩ,p.compatible]

end PureCompatibleCovariance
end Gaussian.Phase
