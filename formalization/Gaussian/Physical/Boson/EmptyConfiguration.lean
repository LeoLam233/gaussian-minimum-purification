import Gaussian.Physical.Boson.CanonicalConfiguration
import Gaussian.Physical.Boson.WeylInjectivity

/-! The genuine zero-mode Schrödinger basis and vacuum. Lebesgue volume is the
unit Dirac measure; completeness also follows directly from actual Weyl separation. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory
open scoped InnerProductSpace

instance emptyConfiguration_probability :
    IsProbabilityMeasure (volume : Measure (CanonicalConfiguration 0)) := by
  refine ⟨?_⟩
  rw [volume_euclideanSpace_eq_dirac]
  simp

def emptyVacuum : Schrodinger (CanonicalConfiguration 0) := Lp.const 2 volume (1:ℂ)

@[simp] theorem emptyVacuum_norm : ‖emptyVacuum‖=1 := by
  change ‖Lp.const 2 (volume : Measure (CanonicalConfiguration 0)) (1:ℂ)‖=1
  rw [Lp.norm_const (p := 2) (μ := volume) (c := (1:ℂ)) (by norm_num)]
  simp [measureReal_def]

lemma empty_orthogonal_eq_zero (ψ : Schrodinger (CanonicalConfiguration 0))
    (h : ⟪emptyVacuum,ψ⟫_ℂ=0) : ψ=0 := by
  have hz : outerOperator ψ emptyVacuum=0 := by
    apply traceClass_eq_zero_of_weyl_zero
    intro q p
    have hq : q=0 := Subsingleton.elim _ _
    have hp : p=0 := Subsingleton.elim _ _
    subst q
    subst p
    rw [tracePairing_outerOperator]
    change ⟪emptyVacuum,weyl 0 0 ψ⟫_ℂ=0
    rw [weyl_zero_apply]
    exact h
  have hn := congrArg norm hz
  rw [norm_outerOperator,emptyVacuum_norm,mul_one,norm_zero] at hn
  exact norm_eq_zero.mp hn

def emptyOccupationBasis : HilbertBasis (Fin 0 → ℕ) ℂ (Schrodinger (CanonicalConfiguration 0)) := by
  classical
  refine HilbertBasis.mkOfOrthogonalEqBot (v := fun _ : Fin 0 → ℕ => emptyVacuum) ?_ ?_
  · rw [orthonormal_iff_ite]
    intro i j
    have h : i=j := Subsingleton.elim _ _
    subst j
    simp [inner_self_eq_norm_sq_to_K]
  · apply le_antisymm ?_ bot_le
    intro ψ hψ
    change ψ=0
    apply empty_orthogonal_eq_zero
    exact hψ _ (Submodule.subset_span ⟨0,rfl⟩)

@[simp] theorem emptyOccupationBasis_apply (k : Fin 0 → ℕ) : emptyOccupationBasis k=emptyVacuum := by
  simp only [emptyOccupationBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

end Gaussian.Physical.Boson
