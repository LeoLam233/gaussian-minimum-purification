import Gaussian.Physical.Boson.GaussianPredicate

/-! Removal and restoration of every finite linear characteristic coefficient by
actual Weyl displacement. No finite squeezing or displacement cutoff is used. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_displacementMean (m : (E × E) →ₗ[ℝ] ℝ) :
    ∃ a b : E, displacementMean a b = m := by
  let f := LinearMap.toContinuousLinearMap (m.comp (LinearMap.inl ℝ E E))
  let g := LinearMap.toContinuousLinearMap (m.comp (LinearMap.inr ℝ E E))
  let b := (InnerProductSpace.toDual ℝ E).symm f
  let c := (InnerProductSpace.toDual ℝ E).symm g
  have hb (q : E) : ⟪b,q⟫_ℝ = m (q,0) := InnerProductSpace.toDual_symm_apply
  have hc (p : E) : ⟪c,p⟫_ℝ = m (0,p) := InnerProductSpace.toDual_symm_apply
  refine ⟨-c,b,?_⟩
  apply LinearMap.ext
  intro z
  change ⟪b,z.1⟫_ℝ - ⟪z.2,-c⟫_ℝ = m z
  rw [inner_neg_right, sub_neg_eq_add, real_inner_comm c z.2, hb, hc, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

theorem IsGaussianWith.exists_centered_displacement {ρ : NormalDensity (Schrodinger E)}
    {m : (E × E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E × E)}
    (h : IsGaussianWith ρ m V) :
    ∃ a b : E, IsGaussianWith (ρ.displace a b) 0 V ∧
      (ρ.displace a b).entropy = ρ.entropy := by
  obtain ⟨a,b,he⟩ := exists_displacementMean (-m)
  refine ⟨a,b,?_,ρ.entropy_displace a b⟩
  simpa only [he, add_neg_cancel] using h.displace a b

theorem IsGaussianWith.exists_prescribed_mean {ρ : NormalDensity (Schrodinger E)}
    {V : LinearMap.BilinForm ℝ (E × E)} (h : IsGaussianWith ρ 0 V)
    (m : (E × E) →ₗ[ℝ] ℝ) :
    ∃ a b : E, IsGaussianWith (ρ.displace a b) m V ∧
      (ρ.displace a b).entropy = ρ.entropy := by
  obtain ⟨a,b,he⟩ := exists_displacementMean m
  refine ⟨a,b,?_,ρ.entropy_displace a b⟩
  simpa only [he, zero_add] using h.displace a b

end Gaussian.Physical.Boson
