import Gaussian.Physical.Boson.CovarianceDomainRealization

/-! The actual bosonic optimization domain over every finite pair of auxiliary
mode counts. The objective is the genuine extended von Neumann entropy;
Gaussian finiteness is a separately proved theorem. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson

abbrev BipartiteDensity (nA nB : ℕ) :=
  NormalDensity (Schrodinger (JointConfiguration (CanonicalConfiguration nA) (CanonicalConfiguration nB)))

abbrev FourPartyDensity (nA nB mA mB : ℕ) :=
  NormalDensity (Schrodinger (FourConfiguration (CanonicalConfiguration nA) (CanonicalConfiguration nB)
    (CanonicalConfiguration mA) (CanonicalConfiguration mB)))

def allFinitePurificationCosts (nA nB : ℕ) (ρ : BipartiteDensity nA nB) : Set ENNReal :=
  {s | ∃ mA mB : ℕ,∃ σ : FourPartyDensity nA nB mA mB,
    IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ=s}

def gaussianPurificationInfimum (nA nB : ℕ) (ρ : BipartiteDensity nA nB) : ENNReal :=
  sInf (allFinitePurificationCosts nA nB ρ)

theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : BipartiteDensity nA nB) (σ : FourPartyDensity nA nB mA mB)
    (hσ : IsSidewisePurifier ρ σ)
    (hmin : ∀ a b : ℕ,∀ τ : FourPartyDensity nA nB a b,
      IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy σ := by
  have hl : IsLeast (allFinitePurificationCosts nA nB ρ) (sidewiseEntropy σ) := by
    refine ⟨⟨mA,mB,σ,hσ,rfl⟩,?_⟩
    rintro s ⟨a,b,τ,hτ,rfl⟩
    exact hmin a b τ hτ
  exact hl.csInf_eq

end Gaussian.Physical.Boson
