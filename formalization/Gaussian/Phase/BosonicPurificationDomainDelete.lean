import Gaussian.Phase.BosonicPurificationDomainMoves
import Gaussian.Phase.BosonicPurificationAuxDelete

/-! Actual finite-total deletion at attained covariance minima. Equality in the
proved local compression comparison produces a genuine globally invariant pure
auxiliary plane, whose actual symplectic complement is the smaller purifier. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

/-- At a true same-total minimum an excess selected side contains an actual
pure auxiliary mode that can be deleted with exactly the same cost. -/
theorem exists_delete_left_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A = p.cost A := by
  obtain ⟨P,hPd,hPn,hWn,hPc,hWd,hcost,hpure⟩ := p.covariance.exists_auxiliary_subcut_selection
    hΩa p.alternating A p.split hA p.split_nondegenerate
    (by simpa only [p.leftModes_dimension] using hExcess)
  let W := ((p.commutator.restrict p.split).orthogonal P).map p.split.subtype
  have hW : (p.commutator.restrict W).Nondegenerate :=
    PureCompatibleCovariance.auxiliary_subcut_nondegenerate p.split _ hWn
  have heq : p.covariance.auxiliaryCutCost A W = p.cost A :=
    le_antisymm hcost (hmin (p.withSplit W hW))
  obtain ⟨r,hr⟩ := hpure heq
  let D := P.map p.split.subtype
  have hDd : finrank ℝ D=2 := by rw [Submodule.finrank_map_subtype_eq,hPd]
  have hDn : (p.commutator.restrict D).Nondegenerate :=
    PureCompatibleCovariance.auxiliary_subcut_nondegenerate p.split P hPn
  have hInv : ∀ x ∈ D.map (LinearMap.inr ℝ E p.Auxiliary),
      p.covariance.generator x ∈ D.map (LinearMap.inr ℝ E p.Auxiliary) :=
    p.covariance.invariant_auxiliary_of_subcut_pure p.split P r hr
  let R := p.commutator.orthogonal D
  have hRn : (p.commutator.restrict R).Nondegenerate :=
    (symplectic_complement_data p.commutator p.alternating p.nondegenerate D hDn).2
  have hWP : W ≤ R := by
    rintro x ⟨y,hy,rfl⟩ z ⟨t,ht,rfl⟩
    exact hy t ht
  let q : BosonicCovariancePurifier V Ω M := {
    Auxiliary := R
    commutator := p.commutator.restrict R
    alternating := fun x => p.alternating x
    nondegenerate := hRn
    mode_count := by
      rw [LinearMap.BilinForm.finrank_orthogonal p.nondegenerate,p.mode_count,hDd]
      omega
    covariance := p.covariance.deleteAuxiliary D hInv
    physical := fun x y => (p.covariance.deleteAuxiliary_physical D hInv x y).trans (p.physical x y)
    split := W.comap R.subtype
    split_nondegenerate := PureCompatibleCovariance.deleteAuxiliary_split_nondegenerate D W hWP hW }
  refine ⟨q,?_⟩
  exact (p.covariance.deleteAuxiliary_cost D W hInv hWP A hA hW).trans heq

/-- Complementing both parties carries an actual attained minimum to the
opposite actual cut; complementary cost is a theorem, not a domain field. -/
theorem complement_minimum (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A) :
    ∀ q : BosonicCovariancePurifier V Ω M,
      p.complement.cost (Ω.orthogonal A) ≤ q.cost (Ω.orthogonal A) := by
  intro q
  have hB := (symplectic_complement_data Ω hΩa hΩn A hA).2
  have hc := q.complement_cost hΩa hΩn (Ω.orthogonal A) hB
  rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩa.isRefl A] at hc
  exact (p.complement_cost hΩa hΩn A hA).trans_le ((hmin q.complement).trans_eq hc)

/-- One actual auxiliary mode can be deleted from any attained minimum above
the physical total, irrespective of which side carries the excess. -/
theorem exists_delete_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ E ≤ 2*M)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A ≤ p.cost A := by
  by_cases ha : finrank ℝ A < 2*p.leftModes
  · obtain ⟨q,hq⟩ := p.exists_delete_left_at_minimum hΩa A hA ha hmin
    exact ⟨q,hq.le⟩
  · have hB := (symplectic_complement_data Ω hΩa hΩn A hA).2
    have hb : finrank ℝ (Ω.orthogonal A) < 2*p.rightModes := by
      rw [LinearMap.BilinForm.finrank_orthogonal hΩn]
      have hp := p.sideModes_sum
      have hAd := A.finrank_le
      omega
    obtain ⟨q,hq⟩ := p.complement.exists_delete_left_at_minimum hΩa (Ω.orthogonal A) hB
      (by simpa using hb) (p.complement_minimum hΩa hΩn A hA hmin)
    refine ⟨q.complement,?_⟩
    have hc := q.complement_cost hΩa hΩn (Ω.orthogonal A) hB
    rw [LinearMap.BilinForm.orthogonal_orthogonal hΩn hΩa.isRefl A] at hc
    exact (hc.trans (hq.trans (p.complement_cost hΩa hΩn A hA))).le

end BosonicCovariancePurifier
end Gaussian.Phase
