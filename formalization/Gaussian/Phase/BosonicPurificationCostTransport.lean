import Gaussian.Phase.BosonicPurificationRigidity
import Gaussian.Phase.BosonicPurificationReindex
import Gaussian.Phase.BosonicPurificationDimension

/-! Covariance cost is invariant under actual changes of coefficient basis and
simultaneous pullback of both forms. These are derived from raw admissibility,
not postulated as state entropy or unitary invariance. -/
noncomputable section
open Module Gaussian.Spectral
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

/-- The original Hermitian-pair cost is independent of the supplied mode basis. -/
theorem bosonFormCost_basis_independent (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) {n : ℕ}
    (e b : Basis (Fin n × Bool) ℝ E) :
    bosonFormCost e V Ω hV hΩa = bosonFormCost b V Ω hV hΩa := by
  have hn : finrank ℝ E = 2*n := by simp [Module.finrank_eq_card_basis e,mul_comm]
  obtain ⟨ν,c,hν,hcΩ,hcV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn hn (Gaussian.Covariance.robertson_inequality hUnc)
  rw [bosonFormCost_eq_canonical e c V Ω hV hΩa ν hν hcV hcΩ,
    bosonFormCost_eq_canonical b c V Ω hV hΩa ν hν hcV hcΩ]

/-- Pullback of both actual forms by an arbitrary real linear equivalence
preserves the independently defined Hermitian-pair cost. -/
theorem bosonFormCost_pullback (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (L : F ≃ₗ[ℝ] E)
    {n : ℕ} (e : Basis (Fin n × Bool) ℝ E) (eF : Basis (Fin n × Bool) ℝ F) :
    bosonFormCost eF (V.compl₁₂ L.toLinearMap L.toLinearMap)
      (Ω.compl₁₂ L.toLinearMap L.toLinearMap)
      ⟨fun x y => hV.eq (L x) (L y)⟩ (fun x => hΩa (L x)) =
      bosonFormCost e V Ω hV hΩa := by
  have hn : finrank ℝ E = 2*n := by simp [Module.finrank_eq_card_basis e,mul_comm]
  obtain ⟨ν,c,hν,hcΩ,hcV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn hn (Gaussian.Covariance.robertson_inequality hUnc)
  rw [bosonFormCost_eq_canonical e c V Ω hV hΩa ν hν hcV hcΩ]
  apply bosonFormCost_eq_canonical eF (c.map L.symm) _ _ _ _ ν hν
  · intro i j
    simpa using hcV i j
  · intro i j
    simpa using hcΩ i j

/-- Full finite-index basis independence, including the disjoint-sum indices
used by actual compact auxiliary frame cuts. -/
theorem bosonFormCost_basis_independent_general
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (e : Basis ι ℝ E) (b : Basis κ ℝ E) :
    bosonFormCost e V Ω hV hΩa = bosonFormCost b V Ω hV hΩa := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  have hn' : finrank ℝ E = 2*n := by omega
  obtain ⟨ν,c,hν,hcΩ,hcV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn hn' (Gaussian.Covariance.robertson_inequality hUnc)
  rw [bosonFormCost_eq_canonical_general e c V Ω hV hΩa ν hν hcV hcΩ,
    bosonFormCost_eq_canonical_general b c V Ω hV hΩa ν hν hcV hcΩ]

/-- Arbitrary finite coefficient indices may be used on either side of the
actual simultaneous pullback of both forms. -/
theorem bosonFormCost_pullback_general
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (L : F ≃ₗ[ℝ] E)
    (e : Basis ι ℝ E) (eF : Basis κ ℝ F) :
    bosonFormCost eF (V.compl₁₂ L.toLinearMap L.toLinearMap)
      (Ω.compl₁₂ L.toLinearMap L.toLinearMap)
      ⟨fun x y => hV.eq (L x) (L y)⟩ (fun x => hΩa (L x)) =
      bosonFormCost e V Ω hV hΩa := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  have hn' : finrank ℝ E = 2*n := by omega
  obtain ⟨ν,c,hν,hcΩ,hcV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn hn' (Gaussian.Covariance.robertson_inequality hUnc)
  rw [bosonFormCost_eq_canonical_general e c V Ω hV hΩa ν hν hcV hcΩ]
  apply bosonFormCost_eq_canonical_general eF (c.map L.symm) _ _ _ _ ν hν
  · intro i j
    simpa using hcV i j
  · intro i j
    simpa using hcΩ i j

/-- Raw admissibility gives nonnegativity of the actual two-form cost. -/
theorem bosonFormCost_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (e : Basis ι ℝ E) :
    0 ≤ bosonFormCost e V Ω hV hΩa := by
  obtain ⟨n,hn⟩ := even_finrank_of_nondegenerate_alternating Ω hΩa hΩn
  have hn' : finrank ℝ E = 2*n := by omega
  obtain ⟨ν,c,hν,hcΩ,hcV⟩ := exists_williamson_basis_bool V Ω hV
    (fun x hx => Gaussian.Covariance.covariance_pos_of_nondegenerate hUnc hΩn hx)
    hΩa hΩn hn' (Gaussian.Covariance.robertson_inequality hUnc)
  rw [bosonFormCost_eq_canonical_general e c V Ω hV hΩa ν hν hcV hcΩ]
  exact Finset.sum_nonneg (fun i _ => Gaussian.Entropy.boson_nonneg (hν i))

end Gaussian.Phase
