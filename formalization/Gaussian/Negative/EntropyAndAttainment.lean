import Gaussian.Physical.Fermion.OrthogonalSpectrum
import Gaussian.Physical.Fermion.GaussianClosure
import Gaussian.Physical.Fermion.ThermalPurity

/-! Kernel-checked negative controls. They refute invalid proof shortcuts, not
the requested physical theorem. -/
set_option autoImplicit false
noncomputable section
open Gaussian.Physical.Fermion Gaussian.Entropy
namespace Gaussian.Negative

theorem zero_mode_quasifree_entropy (ρ : Density 0) (hρ : IsQuasifree ρ) : Sᵥₙ ρ=0 := by
  rw [quasifree_entropy_eq_hermitianCost 0 ρ hρ]
  simp [Gaussian.Attainment.fermionHermitianCost,HermitianMat.trace_eq_re_trace,
    Matrix.trace,MajoranaIndex]

/-- Supplementary deletion control: an arbitrary actual deletion can change entropy.
This is weaker than supplied N1, which concerns entropy-preserving deletion
of a correlated non-pure mode; that separate implication remains to be tested. -/
theorem arbitrary_mode_deletion_changes_entropy :
    ∃ ρ : Density 1,IsQuasifree ρ ∧ Sᵥₙ (prefixRestriction 0 1 ρ)<Sᵥₙ ρ := by
  let ht : ∀ i : Fin 1,(0:ℝ)∈Set.Icc (-1) 1 := fun _ => by norm_num
  let ρ := thermal 1 (fun _ => 0) ht
  have hρ := thermal_isQuasifree 1 (fun _ => 0) ht
  refine ⟨ρ,hρ,?_⟩
  rw [zero_mode_quasifree_entropy _ (isQuasifree_prefixRestriction 0 1 ρ hρ),entropy_thermal]
  simpa only [Fin.sum_univ_one,fermion_one] using
    strictAntiOn_fermion (by norm_num : (0:ℝ)∈Set.Icc 0 1)
      (by norm_num : (1:ℝ)∈Set.Icc 0 1) (by norm_num : (0:ℝ)<1)

/-- N2: arbitrarily small actual Gaussian entropy does not imply exact purity. -/
theorem almost_zero_entropy_need_not_be_pure (ε : ℝ) (hε : 0<ε) :
    ∃ ρ : Density 1,IsQuasifree ρ ∧ 0<Sᵥₙ ρ ∧ Sᵥₙ ρ<ε ∧ ¬∃ ψ,ρ=MState.pure ψ := by
  obtain ⟨δ,hδ,hc⟩ := Metric.continuousAt_iff.mp continuous_fermion.continuousAt ε hε
  let q := min (δ/2) (1/2:ℝ)
  have hq : 0<q := lt_min (by linarith) (by norm_num)
  have hqδ : q<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hqhalf : q≤(1/2:ℝ) := min_le_right _ _
  let t := 1-q
  have ht0 : 0<t := by dsimp [t]; linarith
  have ht1 : t<1 := by dsimp [t]; linarith
  have hti : t∈Set.Icc (0:ℝ) 1 := ⟨ht0.le,ht1.le⟩
  have htp : 0<fermion t := by
    simpa only [fermion_one] using strictAntiOn_fermion hti (by norm_num) ht1
  have hnear : dist t (1:ℝ)<δ := by
    rw [Real.dist_eq]
    have he : t-1 = -q := by dsimp [t]; ring
    rw [he,abs_neg,abs_of_pos hq]
    exact hqδ
  have hsmall : fermion t<ε := by
    have hh := hc hnear
    simpa only [Real.dist_eq,fermion_one,sub_zero,abs_of_pos htp] using hh
  let ht : ∀ i : Fin 1,t∈Set.Icc (-1:ℝ) 1 := fun _ => ⟨by linarith,ht1.le⟩
  let ρ := thermal 1 (fun _ => t) ht
  have hS : Sᵥₙ ρ=fermion t := by rw [entropy_thermal]; simp
  refine ⟨ρ,thermal_isQuasifree 1 (fun _ => t) ht,by rw [hS]; exact htp,
    by rw [hS]; exact hsmall,?_⟩
  intro hp
  have he := (thermal_pure_iff_endpoints 1 (fun _ => t) ht).mp hp 0
  rcases he with he | he <;> linarith

/-- N6: every finite-size problem can attain its minimum while the union over
all finite sizes has no attained minimum. -/
theorem fixed_size_attainment_does_not_imply_global :
    (∀ M : ℕ,∃ x : Unit,∀ y : Unit,(1:ℝ)/(M+1)≤1/(M+1)) ∧
    ¬∃ M : ℕ,∀ L : ℕ,(1:ℝ)/(M+1)≤1/(L+1) := by
  constructor
  · intro M; exact ⟨(),fun _ => le_rfl⟩
  · rintro ⟨M,hM⟩
    have hpos : 0<(M:ℝ)+1 := by positivity
    have hlt : (1:ℝ)/((M:ℝ)+2)<1/((M:ℝ)+1) :=
      one_div_lt_one_div_of_lt hpos (by linarith)
    have hh := hM (M+1)
    push_cast at hh
    have he : (M:ℝ)+1+1=(M:ℝ)+2 := by ring
    rw [he] at hh
    exact (not_le_of_gt hlt) hh

end Gaussian.Negative
