import Gaussian.Physical.Fermion.SidewiseDomain
import Gaussian.Physical.Fermion.SuffixRestriction
import Gaussian.Physical.Fermion.CountTransport

noncomputable section
namespace Gaussian.Physical.Fermion

@[simp] theorem modeCountCast_entropy {n m : ℕ} (h : n=m) (ρ : Density n) :
    Sᵥₙ (modeCountCast h ρ)=Sᵥₙ ρ := by subst m; rfl

/-- Transport a suffix trace through two equal retained-count descriptions;
all input transports are count equalities, not physical permutations. -/
theorem suffixRestriction_cast_prefix_eq {n k K l : ℕ} (h : k=K)
    (hk : n=l+k) (hK : n=l+K) (ρ : Density n) :
    suffixRestriction k l (modeCountCast hk ρ)=suffixRestriction K l (modeCountCast hK ρ) := by
  subst K
  rfl

/-- The sidewise entropy is independent of proof-level equal descriptions of
its B' mode count. -/
theorem sidewiseEntropy_cast_B_eq (nA nB mA : ℕ) {n b B : ℕ} (h : b=B)
    (hb : n=(mA+b)+(nA+nB)) (hB : n=(mA+B)+(nA+nB)) (ρ : Density n) :
    sidewiseEntropy nA nB mA b (modeCountCast hb ρ)=
      sidewiseEntropy nA nB mA B (modeCountCast hB ρ) := by
  subst B
  rfl

end Gaussian.Physical.Fermion
