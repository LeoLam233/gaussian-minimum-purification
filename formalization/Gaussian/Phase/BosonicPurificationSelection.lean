import Gaussian.Phase.BosonicPurificationRigidity
import Gaussian.Phase.BosonicPurificationDimension

/-! Raw bosonic covariance selection on an excess auxiliary space. The selected
factor, its retained complement, and cost comparison are derived from raw
uncertainty. Equality yields genuine pure covariance on the selected factor. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A Boolean mode basis constructed from an exact real dimension count. -/
def modeBasisOfFinrankEq {n : ℕ} (hn : finrank ℝ E = 2*n) :
    Basis (Fin n × Bool) ℝ E :=
  (Module.finBasis ℝ E).reindex (Fintype.equivOfCardEq (by simp [hn,mul_comm]))

/-- Actual covariance-only selection: a protected physical subspace is retained,
a complete symplectic mode is removed, cost decreases, and equality makes the
removed covariance pure. There are no spectrum or physical-state hypotheses. -/
theorem exists_bosonic_covariance_selection (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (A : Submodule ℝ E)
    (hExcess : finrank ℝ E < 2*finrank ℝ (Ω.orthogonal A))
    {n : ℕ} (e : Basis (Fin n × Bool) ℝ E) :
    ∃ P : Submodule ℝ E,
      finrank ℝ P = 2 ∧ P ≤ Ω.orthogonal A ∧ A ≤ Ω.orthogonal P ∧
      (Ω.restrict P).Nondegenerate ∧ (Ω.restrict (Ω.orthogonal P)).Nondegenerate ∧
      IsCompl P (Ω.orthogonal P) ∧ finrank ℝ (Ω.orthogonal P) = 2*(n-1) ∧
      ∃ eU : Basis (Fin (n-1) × Bool) ℝ (Ω.orthogonal P),
        bosonFormCost eU (V.restrict (Ω.orthogonal P)) (Ω.restrict (Ω.orthogonal P))
            (hV.restrict _) (fun x => hΩa x) ≤ bosonFormCost e V Ω hV hΩa ∧
        (bosonFormCost eU (V.restrict (Ω.orthogonal P)) (Ω.restrict (Ω.orthogonal P))
            (hV.restrict _) (fun x => hΩa x) = bosonFormCost e V Ω hV hΩa →
          ∃ p : PureCompatibleCovariance (Ω.restrict P), p.form = V.restrict P) := by
  obtain ⟨d,hLower⟩ := Gaussian.Covariance.exists_bosonicAdaptation_from_uncertainty
    V Ω hV hΩa hΩn (even_finrank_of_nondegenerate_alternating Ω hΩa hΩn) hUnc
  obtain ⟨v,hv,hPA,hPdim,hP,hU,hPn,hUn,hCompl,hOrth⟩ :=
    d.exists_selected_plane (Ω.orthogonal A) hExcess
  let P := d.selectedPlane v
  have hAP : A ≤ Ω.orthogonal P := by
    intro a ha p hp
    exact hΩa.isRefl a p (hPA hp a ha)
  have hn : finrank ℝ E = 2*n := by simp [Module.finrank_eq_card_basis e,mul_comm]
  have hdim : finrank ℝ (Ω.orthogonal P) = 2*(n-1) := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hCompl
    change finrank ℝ P + finrank ℝ (Ω.orthogonal P) = finrank ℝ E at hsum
    change finrank ℝ P = 2 at hPdim
    omega
  let eU := modeBasisOfFinrankEq hdim
  refine ⟨P,hPdim,hPA,hAP,hPn,hUn,hCompl,hdim,eU,?_,?_⟩
  · exact d.restricted_formCost_le hΩa hLower (Ω.orthogonal P) hU e eU
  · intro he
    have hpure := d.exists_pure_discarded_of_formCost_eq hΩa hLower
      (Ω.orthogonal P) hU e eU he
    rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩa.isRefl P] at hpure
    exact hpure

end Gaussian.Phase
