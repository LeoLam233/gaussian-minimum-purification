import Gaussian.Physical.Boson.AllFiniteDomain
import Gaussian.Phase.BosonicPurificationMinimum

/-! Actual normal finite-mode bosonic Gaussian minimum purification. The global
comparison ranges over all finite sidewise auxiliary counts, and the witness
has the matched counts. Raw covariance optimization is connected to actual
states, actual partial trace and actual CFC entropy by proved equivalences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase WithLp

/-- The actual bosonic primary theorem, including zero parties, pure/repeated
normal parameters, arbitrary finite squeezing and arbitrary finite Weyl means. -/
theorem exists_matched_global_gaussian_purification (nA nB : ℕ)
    (ρ : BipartiteDensity nA nB) (hρ : IsGaussian ρ) :
    ∃ σ : FourPartyDensity nA nB nA nB,
      IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
      sidewiseEntropy σ=gaussianPurificationInfimum nA nB ρ ∧
      ∀ mA mB : ℕ,∀ τ : FourPartyDensity nA nB mA mB,
        IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ := by
  obtain ⟨m,V,h⟩ := hρ
  let A := CanonicalConfiguration nA
  let B := CanonicalConfiguration nB
  have hA : finrank ℝ A=nA := by simp [A,CanonicalConfiguration]
  have hB : finrank ℝ B=nB := by simp [B,CanonicalConfiguration]
  have hAB : finrank ℝ (JointConfiguration A B)=nA+nB := by
    rw [(WithLp.linearEquiv 2 ℝ (A×B)).finrank_eq,Module.finrank_prod,hA,hB]
  have hd : finrank ℝ (JointConfiguration A B×JointConfiguration A B)=2*(nA+nB) := by
    rw [Module.finrank_prod,hAB]
    omega
  have hAd : finrank ℝ (physicalPhaseSubspace A B)=2*nA := by
    rw [physicalPhaseSubspace_finrank,hA]
  obtain ⟨p,hpA,hpB,hmin⟩ := exists_bosonic_covariance_allFinite_matched_minimum
    V (weylSymplecticForm (JointConfiguration A B)) h.1 weylSymplecticForm_isAlt
    weylSymplecticForm_nondegenerate h.uncertainty (physicalPhaseSubspace A B)
    (physicalPhaseSubspace_nondegenerate A B) nA nB hd hAd
  have hreal := covariancePurifier_exists_sidewise_realization h p
  rw [hpA,hpB] at hreal
  obtain ⟨a,b,hab,ha,hb,σ,hσ,hfin,hcost⟩ := hreal
  subst a
  subst b
  have hm : ∀ mA mB : ℕ,∀ τ : FourPartyDensity nA nB mA mB,
      IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ := by
    intro mA mB τ hτ
    obtain ⟨q,hqA,hqB,hτfin,hτcost⟩ := hτ.exists_covariancePurifier h
    have hr : (sidewiseEntropy σ).toReal≤(sidewiseEntropy τ).toReal := by
      rw [hcost,hτcost]
      exact hmin _ q
    calc
      sidewiseEntropy σ=ENNReal.ofReal (sidewiseEntropy σ).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (sidewiseEntropy τ).toReal := ENNReal.ofReal_le_ofReal hr
      _ = sidewiseEntropy τ := ENNReal.ofReal_toReal hτfin
  exact ⟨σ,hσ,hfin,(infimum_eq_of_global_sidewise_witness nA nB nA nB ρ σ hσ hm).symm,hm⟩

theorem gaussianPurificationInfimum_ne_top (nA nB : ℕ)
    (ρ : BipartiteDensity nA nB) (hρ : IsGaussian ρ) :
    gaussianPurificationInfimum nA nB ρ≠⊤ := by
  obtain ⟨σ,hσ,hfin,he,hmin⟩ := exists_matched_global_gaussian_purification nA nB ρ hρ
  rwa [← he]

end Gaussian.Physical.Boson
