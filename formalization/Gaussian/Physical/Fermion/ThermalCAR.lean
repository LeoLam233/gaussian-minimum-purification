import Gaussian.Physical.Fermion.ThermalWard
import Gaussian.Physical.Fermion.WardSpace

/-! The proved endpoint-safe thermal Ward identities extend to every real
linear Majorana head by linear-subspace closure. -/
noncomputable section
open scoped Matrix BigOperators
namespace Gaussian.Physical.Fermion

theorem majorana_false_eq_ann_add_creation (n : ℕ) (i : Fin n) :
    majorana n (i,false) = annihilation n i + creation n i := by
  rw [annihilation_majorana,creation_majorana]
  ext a b
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem majorana_true_eq_creation_sub_ann (n : ℕ) (i : Fin n) :
    majorana n (i,true) = Complex.I • (creation n i-annihilation n i) := by
  rw [annihilation_majorana,creation_majorana]
  ext a b
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

theorem majorana_mem_scalarAnticommutant (n : ℕ) (a : MajoranaIndex n) (v : CoefficientSpace n) :
    majorana n a ∈ scalarAnticommutant (linearMajorana n v) := by
  refine ⟨2*(v a : ℂ),?_⟩
  simpa only [linearMajorana,add_comm] using
    majoranaSum_car_generator n (fun b => (v b : ℂ)) a

theorem annihilation_mem_scalarAnticommutant (n : ℕ) (i : Fin n) (v : CoefficientSpace n) :
    annihilation n i ∈ scalarAnticommutant (linearMajorana n v) := by
  rw [annihilation_majorana]
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · exact majorana_mem_scalarAnticommutant n (i,false) v
  · exact Submodule.smul_mem _ _ (majorana_mem_scalarAnticommutant n (i,true) v)

theorem creation_mem_scalarAnticommutant (n : ℕ) (i : Fin n) (v : CoefficientSpace n) :
    creation n i ∈ scalarAnticommutant (linearMajorana n v) := by
  rw [creation_majorana]
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact majorana_mem_scalarAnticommutant n (i,false) v
  · exact Submodule.smul_mem _ _ (majorana_mem_scalarAnticommutant n (i,true) v)

/-- Each actual thermal annihilator obeys Wick's first-slot rule for arbitrary
linear Majorana tails, including zero thermal weights. -/
theorem thermal_annihilation_mem_Ward (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n)
    (l : List (CoefficientSpace n)) (hl : Odd l.length) :
    annihilation n i ∈ wordWardSpace (thermal n t ht).m (l.map (linearMajorana n)) := by
  apply weighted_head_mem_of_scalar_anticommutators (thermal n t ht).m (annihilation n i)
    (emptyWeight (t i)) (occupiedWeight (t i)) (thermal n t ht).tr'
    (thermal_weights_sum _) (thermal_annihilation_balance n t ht i)
    (l.map (linearMajorana n)) ?_ (by simpa only [List.length_map] using hl)
  intro X hX
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hX
  exact annihilation_mem_scalarAnticommutant n i v

theorem thermal_creation_mem_Ward (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (i : Fin n)
    (l : List (CoefficientSpace n)) (hl : Odd l.length) :
    creation n i ∈ wordWardSpace (thermal n t ht).m (l.map (linearMajorana n)) := by
  apply weighted_head_mem_of_scalar_anticommutators (thermal n t ht).m (creation n i)
    (occupiedWeight (t i)) (emptyWeight (t i)) (thermal n t ht).tr'
    (by rw [add_comm,thermal_weights_sum]) (thermal_creation_balance n t ht i)
    (l.map (linearMajorana n)) ?_ (by simpa only [List.length_map] using hl)
  intro X hX
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hX
  exact creation_mem_scalarAnticommutant n i v

/-- Every real linear CAR head belongs to the actual thermal Ward subspace. -/
theorem thermal_linearMajorana_mem_Ward (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (v : CoefficientSpace n)
    (l : List (CoefficientSpace n)) (hl : Odd l.length) :
    linearMajorana n v ∈ wordWardSpace (thermal n t ht).m (l.map (linearMajorana n)) := by
  let S := wordWardSpace (thermal n t ht).m (l.map (linearMajorana n))
  have ha (i : Fin n) : annihilation n i ∈ S := thermal_annihilation_mem_Ward n t ht i l hl
  have hc (i : Fin n) : creation n i ∈ S := thermal_creation_mem_Ward n t ht i l hl
  have hm (a : MajoranaIndex n) : majorana n a ∈ S := by
    rcases a with ⟨i,b⟩
    cases b
    · rw [majorana_false_eq_ann_add_creation]
      exact S.add_mem (ha i) (hc i)
    · rw [majorana_true_eq_creation_sub_ann]
      exact S.smul_mem _ (S.sub_mem (hc i) (ha i))
  unfold linearMajorana majoranaSum
  exact S.sum_mem (fun a _ => S.smul_mem _ (hm a))

end Gaussian.Physical.Fermion
