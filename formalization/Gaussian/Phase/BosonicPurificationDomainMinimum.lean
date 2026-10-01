import Gaussian.Phase.BosonicPurificationDomain
import Gaussian.Phase.BosonicPurificationStandardLift
import Gaussian.Phase.BosonicPurificationSubspaceMinimum
import Gaussian.Phase.BosonicPurificationReference

/-! Genuine fixed-total covariance attainment on the full raw purification
domain. Reference parametrization is justified by the actual auxiliary orbit,
and compact attainment covers every nondegenerate auxiliary split. -/
universe u
noncomputable section
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Every sufficiently large finite auxiliary total admits an actual global
minimum over all raw pure covariance purifiers and all actual sidewise splits. -/
theorem exists_bosonic_covariance_fixedTotal_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate) (M : ℕ)
    (hsize : finrank ℝ E ≤ 2*M) :
    ∃ p : BosonicCovariancePurifier V Ω M,
      ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A := by
  let F := StandardBosonicSpaceLift.{u} M
  let σ := standardSymplecticFormLift.{u} M
  let r := standardPureCovarianceLift.{u} M
  obtain ⟨p₀,hp₀⟩ := exists_bosonic_reference_with_auxiliary V Ω σ hV hΩa
    r.commutator_alternating hΩn r.commutator_nondegenerate hUnc
    (by simpa only [finrank_standardBosonicSpaceLift] using hsize)
  obtain ⟨S,hS,hmin⟩ := p₀.exists_auxiliaryCutCost_minimum A hA
  let p : BosonicCovariancePurifier V Ω M := {
    Auxiliary := F
    commutator := σ
    alternating := r.commutator_alternating
    nondegenerate := r.commutator_nondegenerate
    mode_count := finrank_standardBosonicSpaceLift M
    covariance := p₀
    physical := hp₀
    split := S
    split_nondegenerate := hS }
  refine ⟨p,?_⟩
  intro q
  obtain ⟨Q,hQ,hcov⟩ := exists_pure_covariance_auxiliary_equiv Ω q.commutator σ hΩn
    q.covariance p₀ (q.mode_count.trans (finrank_standardBosonicSpaceLift M).symm)
    (fun x y => (q.physical x y).trans (hp₀ x y).symm)
  have hT : (σ.restrict (q.split.map Q.toLinearMap)).Nondegenerate :=
    nondegenerate_of_form_equiv (q.commutator.restrict q.split)
      (σ.restrict (q.split.map Q.toLinearMap)) q.split_nondegenerate (Q.submoduleMap q.split)
      (fun x y => hQ x y)
  have hc := q.covariance.auxiliaryCutCost_transport p₀ Q hQ hcov A q.split hA q.split_nondegenerate
  exact (hmin (q.split.map Q.toLinearMap) hT).trans_eq hc.symm

end Gaussian.Phase
