import Gaussian.Physical.Boson.GaussianPredicate
import Gaussian.Physical.Boson.WeylSymplectic

/-! An implementation relation is equality of actual bounded Schrödinger
operators, not a state/entropy conclusion inserted into data. Every use must
supply an independently constructed unitary and prove this relation. -/
noncomputable section
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def WeylImplements (R : (E×E) ≃ₗ[ℝ] (E×E))
    (U : unitary (Schrodinger E →L[ℂ] Schrodinger E)) : Prop :=
  ∀ z, star (U : Schrodinger E →L[ℂ] Schrodinger E) *
    weylOperator z.1 z.2 * U = weylOperator (R z).1 (R z).2

theorem WeylImplements.characteristic {R : (E×E) ≃ₗ[ℝ] (E×E)}
    {U : unitary (Schrodinger E →L[ℂ] Schrodinger E)} (h : WeylImplements R U)
    (ρ : NormalDensity (Schrodinger E)) (z : E×E) :
    (ρ.conjugate U).characteristic z.1 z.2 = ρ.characteristic (R z).1 (R z).2 := by
  unfold NormalDensity.characteristic
  rw [NormalDensity.expect_conjugate,h z]

theorem WeylImplements.gaussian {R : (E×E) ≃ₗ[ℝ] (E×E)}
    {U : unitary (Schrodinger E →L[ℂ] Schrodinger E)} (h : WeylImplements R U)
    {ρ : NormalDensity (Schrodinger E)} {m : (E×E) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (E×E)} (hρ : IsGaussianWith ρ m V) :
    IsGaussianWith (ρ.conjugate U) (m.comp R.toLinearMap)
      (V.compl₁₂ R.toLinearMap R.toLinearMap) := by
  refine ⟨⟨fun x y => hρ.1.eq (R x) (R y)⟩,?_⟩
  intro q p
  rw [h.characteristic ρ (q,p),hρ.2 (R (q,p)).1 (R (q,p)).2]
  rfl

/-- State entropy invariance is a theorem about the actual density operator. -/
theorem WeylImplements.entropy {R : (E×E) ≃ₗ[ℝ] (E×E)}
    {U : unitary (Schrodinger E →L[ℂ] Schrodinger E)} (_h : WeylImplements R U)
    (ρ : NormalDensity (Schrodinger E)) : (ρ.conjugate U).entropy=ρ.entropy :=
  ρ.entropy_conjugate U

end Gaussian.Physical.Boson
