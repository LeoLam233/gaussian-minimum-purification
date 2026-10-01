import Gaussian.Physical.Fermion.PhysicalSubspace
import Gaussian.Physical.Fermion.ThermalGenerator

/-! N5: a genuine pure product Gaussian covariance has multiple available
invariant complex lines. Selection is existential, not unique. -/
set_option autoImplicit false
noncomputable section
open Module Gaussian.Phase Gaussian.Physical.Fermion
namespace Gaussian.Negative

theorem invariant_plane_selection_need_not_be_unique :
    ∃ (J : OrthogonalComplexStructure (CoefficientSpace 2))
      (P Q : Submodule ℝ (CoefficientSpace 2)),
      P≠Q ∧ finrank ℝ P=2 ∧ finrank ℝ Q=2 ∧ J.IsInvariant P ∧ J.IsInvariant Q := by
  let ht : ∀ i : Fin 2,(1:ℝ)∈Set.Icc (-1) 1 := fun _ => by norm_num
  let ρ := thermal 2 (fun _ => 1) ht
  have hp : IsPureQuasifree ρ :=
    ⟨thermal_isQuasifree 2 (fun _ => 1) ht,
      (thermal_pure_iff_endpoints 2 (fun _ => 1) ht).mpr (fun _ => Or.inl rfl)⟩
  let J := pureCovarianceComplexStructure ρ hp
  have hJ (i : Fin 2) : J (coefficientBasis 2 (i,false))=coefficientBasis 2 (i,true) := by
    change covarianceGenerator (thermal 2 (fun _ => 1) ht) _=_
    rw [thermalGenerator_false,one_smul]
  let v := coefficientBasis 2 (0,false)
  let w := coefficientBasis 2 (1,false)
  have hv : v≠0 := by
    intro h
    have hh := congrArg (fun x : CoefficientSpace 2 => x (0,false)) h
    norm_num [v,coefficientBasis,PiLp.single_apply] at hh
  have hw : w≠0 := by
    intro h
    have hh := congrArg (fun x : CoefficientSpace 2 => x (1,false)) h
    norm_num [w,coefficientBasis,PiLp.single_apply] at hh
  refine ⟨J,J.plane v,J.plane w,?_,J.finrank_plane hv,J.finrank_plane hw,
    J.plane_invariant v,J.plane_invariant w⟩
  intro he
  have hz : ∀ x ∈ J.plane w,x (0,false)=0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · norm_num [w,coefficientBasis,PiLp.single_apply]
      · have heq : x=J w := Set.mem_singleton_iff.mp hx
        rw [heq]
        change (J (coefficientBasis 2 (1,false))) (0,false)=0
        rw [hJ]
        norm_num [coefficientBasis,PiLp.single_apply]
    | zero => rfl
    | add x y hx hy hx' hy' => simp only [PiLp.add_apply,hx',hy',add_zero]
    | smul r x hx hx' => simp only [PiLp.smul_apply,hx',smul_zero]
  have hm : v ∈ J.plane w := he ▸ Submodule.subset_span (Set.mem_insert v {J v})
  have hh := hz v hm
  norm_num [v,coefficientBasis,PiLp.single_apply] at hh

end Gaussian.Negative
