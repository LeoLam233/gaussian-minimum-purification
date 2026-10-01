import Gaussian.Phase.BosonicPurificationDomainMinimum
import Gaussian.Phase.BosonicPurificationDomainDelete
import Gaussian.Phase.BosonicPurificationAuxPadding
import Gaussian.Optimization.MatchedIteration

/-! The covariance-only all-finite/matched bosonic purification theorem.
Every proof obligation of compact attainment, actual optimal deletion, pure
padding and finite reallocation is discharged on the raw covariance domain.
The canonical-coordinate conclusion is obtained by a proved cost-preserving
transport, so the comparison domain contains every finite auxiliary symplectic
space and every actual nondegenerate split. Actual state realization and density
entropy are separate theorems and are not asserted by this module. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A matched raw pure covariance attains a minimum against every finite
auxiliary total, carrier and nondegenerate sidewise split. -/
theorem exists_bosonic_covariance_allFinite_matched_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (nA nB : ℕ) (hd : finrank ℝ E=2*(nA+nB)) (hAd : finrank ℝ A=2*nA) :
    ∃ p : BosonicCovariancePurifier V Ω (nA+nB),
      p.leftModes=nA ∧ p.rightModes=nB ∧
      ∀ M : ℕ, ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A := by
  let D := BosonicCovariancePurifier V Ω
  let c := fun M (p : D M) => p.cost A
  obtain ⟨p,hp⟩ := Gaussian.Optimization.global_attained_from_optimal_deletion D c (nA+nB)
    (fun M hM => exists_bosonic_covariance_fixedTotal_minimum V Ω hV hΩa hΩn hUnc A hA M
      (by rw [hd]; omega))
    (fun M hM p hmin => p.exists_delete_at_minimum hΩa hΩn A hA
      (by rw [hd]; omega) hmin)
    (fun M hM p => ⟨p.pad (Nat.le_of_lt hM),(p.pad_cost (Nat.le_of_lt hM) A hA).le⟩)
  have hBd : finrank ℝ (Ω.orthogonal A)=2*nB := by
    rw [LinearMap.BilinForm.finrank_orthogonal hΩn,hd,hAd]
    omega
  obtain ⟨q,hq,hcost⟩ := Gaussian.Optimization.exists_matched_cost_le_of_unit_moves
    (fun r : D (nA+nB) => r.leftModes) (fun r => r.cost A) nA
    (fun r hr => r.exists_move_right hΩa hΩn A hA (by
      rw [hBd]
      have h:=r.sideModes_sum
      omega))
    (fun r hr => r.exists_move_left hΩa A hA (by rw [hAd]; omega)) p
  refine ⟨q,hq,?_,fun M r => hcost.trans (hp M r)⟩
  have h:=q.sideModes_sum
  omega

/-- The same attained all-finite minimum in literal canonical sidewise counts.
Both the physical covariance and the actual two-form objective are preserved by
the proved symplectic coordinate transport. -/
theorem exists_bosonic_covariance_canonical_matched_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (nA nB : ℕ) (hd : finrank ℝ E=2*(nA+nB)) (hAd : finrank ℝ A=2*nA) :
    ∃ p : PureCompatibleCovariance
        (productForm Ω (productForm (standardSymplecticForm (EuclideanSpace ℝ (Fin nA)))
          (standardSymplecticForm (EuclideanSpace ℝ (Fin nB))))),
      (∀ x y, p.form (x,0) (y,0)=V x y) ∧
      ∀ M : ℕ, ∀ q : BosonicCovariancePurifier V Ω M,
        p.auxiliaryCutCost A
          (LinearMap.inl ℝ (StandardBosonicSpace nA) (StandardBosonicSpace nB)).range ≤ q.cost A := by
  obtain ⟨q,hqA,hqB,hmin⟩ := exists_bosonic_covariance_allFinite_matched_minimum
    V Ω hV hΩa hΩn hUnc A hA nA nB hd hAd
  obtain ⟨a,b,hab,ha,hb,p,hphys,hcost⟩ := q.exists_canonical_sidewise_transport A hA
  have hea : a=nA := ha.trans hqA
  have heb : b=nB := hb.trans hqB
  clear ha hb
  subst a
  subst b
  exact ⟨p,hphys,fun M r => hcost.trans_le (hmin M r)⟩

end Gaussian.Phase
