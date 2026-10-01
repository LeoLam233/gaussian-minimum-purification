import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Finite real coefficient-space geometry.  All results here are geometric results
for an explicitly supplied orthogonal complex structure.  Existence from a raw
covariance is a separate theorem, never an assumption hidden in a state type. -/
noncomputable section
open Module
open scoped RealInnerProductSpace

namespace Gaussian.Phase

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal real complex structure; no covariance or state assertion is a field. -/
structure OrthogonalComplexStructure where
  equiv : E ≃ₗᵢ[ℝ] E
  square_neg : ∀ x, equiv (equiv x) = -x

namespace OrthogonalComplexStructure
variable {E} (J : OrthogonalComplexStructure E)

instance : CoeFun (OrthogonalComplexStructure E) (fun _ => E → E) := ⟨fun J => J.equiv⟩

abbrev linear : E →ₗ[ℝ] E := J.equiv.toLinearEquiv.toLinearMap

def image (A : Submodule ℝ E) : Submodule ℝ E := A.map J.linear

def IsInvariant (A : Submodule ℝ E) : Prop := ∀ x ∈ A, J x ∈ A

@[simp] theorem apply_apply (x : E) : J (J x) = -x := J.square_neg x
@[simp] theorem apply_zero : J 0 = 0 := J.equiv.map_zero
@[simp] theorem apply_neg (x : E) : J (-x) = -J x := J.equiv.map_neg x
@[simp] theorem apply_add (x y : E) : J (x+y) = J x + J y := J.equiv.map_add x y
@[simp] theorem apply_smul (r : ℝ) (x : E) : J (r • x) = r • J x := J.equiv.map_smul r x
@[simp] theorem inner_map_map (x y : E) : ⟪J x, J y⟫ = ⟪x,y⟫ := J.equiv.inner_map_map x y

/-- Orthogonal complex structures are skew-adjoint. -/
theorem inner_map_left (x y : E) : ⟪J x,y⟫ = -⟪x,J y⟫ := by
  have h := J.inner_map_map x (J y)
  have h' : -⟪J x,y⟫ = ⟪x,J y⟫ := by simpa using h
  linarith

@[simp] theorem inner_self_map (x : E) : ⟪x,J x⟫ = 0 := by
  have h := J.inner_map_left x x
  have hc := real_inner_comm (J x) x
  linarith

@[simp] theorem image_image (A : Submodule ℝ E) : J.image (J.image A) = A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z,hz,rfl⟩,rfl⟩
    simpa using A.neg_mem hz
  · intro hx
    exact ⟨J (-x), ⟨-x,A.neg_mem hx,rfl⟩, by simp⟩

/-- The intersection used to select a complete mode is invariant. -/
theorem intersection_invariant (C : Submodule ℝ E) : J.IsInvariant (C ⊓ J.image C) := by
  rintro x ⟨hx, y, hy, hxy⟩
  constructor
  · change J.linear y = x at hxy
    subst x
    simpa using C.neg_mem hy
  · exact ⟨x,hx,rfl⟩

/-- Canonical crosswalk from the J-hull of the physical space to auxiliary selection. -/
theorem hull_orthogonal (A : Submodule ℝ E) :
    (A ⊔ J.image A)ᗮ = Aᗮ ⊓ J.image Aᗮ := by
  rw [← Submodule.inf_orthogonal]
  exact congrArg (fun B => Aᗮ ⊓ B) (A.map_orthogonal_equiv J.equiv).symm

/-- A J-invariant subspace has J-invariant Euclidean (or compatible-metric) complement. -/
theorem orthogonal_invariant {A : Submodule ℝ E} (hA : J.IsInvariant A) :
    J.IsInvariant Aᗮ := by
  intro x hx a ha
  have h := hx (J a) (hA a ha)
  have hs := J.inner_map_left a x
  linarith

/-- The selected real two-plane. -/
def plane (v : E) : Submodule ℝ E := Submodule.span ℝ ({v,J v} : Set E)

theorem plane_le {C : Submodule ℝ E} {v : E} (hv : v ∈ C) (hJv : J v ∈ C) :
    J.plane v ≤ C := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hv
  · simpa only [Set.mem_singleton_iff] using hx ▸ hJv

theorem plane_invariant (v : E) : J.IsInvariant (J.plane v) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have hx' : x = J v := Set.mem_singleton_iff.mp hx
      rw [hx', J.apply_apply]
      exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert _ _))
  | zero => simp [plane]
  | add x y hx hy hx' hy' => simpa using Submodule.add_mem _ hx' hy'
  | smul r x hx hx' => simpa using Submodule.smul_mem _ r hx'

theorem pair_linearIndependent {v : E} (hv : v ≠ 0) :
    LinearIndependent ℝ ![v,J v] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using J.equiv.injective.ne hv
  · intro a ha
    have h := congrArg (fun x : E => ⟪v,x⟫) ha
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, inner_smul_right,
      J.inner_self_map, mul_zero] at h
    exact hv (inner_self_eq_zero.mp h.symm)

/-- A nonzero vector and its J-image span exactly two real dimensions. -/
theorem finrank_plane {v : E} (hv : v ≠ 0) : finrank ℝ (J.plane v) = 2 := by
  have h := finrank_span_eq_card (J.pair_linearIndependent hv)
  have hr : Set.range ![v,J v] = ({v,J v} : Set E) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  change finrank ℝ ↥(Submodule.span ℝ (Set.range ![v,J v])) = 2 at h
  rw [hr] at h
  exact h

/-- A dimension lower bound retaining all multiplicities and allowing zero-dimensional spaces. -/
theorem intersection_dimension [FiniteDimensional ℝ E] (C : Submodule ℝ E) :
    2 * finrank ℝ C ≤ finrank ℝ E + finrank ℝ ↥(C ⊓ J.image C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq C (J.image C)
  have hm : finrank ℝ ↥(J.image C) = finrank ℝ C := J.equiv.toLinearEquiv.finrank_map_eq C
  have hu := Submodule.finrank_le (C ⊔ J.image C)
  omega

/-- An excess auxiliary coefficient space contains a genuine invariant real two-plane. -/
theorem exists_plane_of_excess [FiniteDimensional ℝ E] (C : Submodule ℝ E)
    (hC : finrank ℝ E < 2 * finrank ℝ C) :
    ∃ v : E, v ≠ 0 ∧ J.plane v ≤ C ∧ finrank ℝ (J.plane v) = 2 ∧
      J.IsInvariant (J.plane v) ∧ J.IsInvariant (J.plane v)ᗮ := by
  have hd := J.intersection_dimension C
  have hn : C ⊓ J.image C ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp hn
  refine ⟨v,hv0,J.plane_le hv.1 (J.intersection_invariant C v hv).1,
    J.finrank_plane hv0,J.plane_invariant v,?_⟩
  exact J.orthogonal_invariant (J.plane_invariant v)

/-- The symplectic form associated with the compatible metric and J.
The sign is fixed by Ω(x,Jy)=g(x,y), as required for coefficient vectors. -/
def symplecticForm : LinearMap.BilinForm ℝ E := -(innerₗ E).compl₂ J.linear

@[simp] theorem symplecticForm_apply (x y : E) :
    J.symplecticForm x y = -⟪x,J y⟫ := rfl

@[simp] theorem symplecticForm_map_right (x y : E) :
    J.symplecticForm x (J y) = ⟪x,y⟫ := by simp

/-- The compatible bilinear metric is strictly positive on nonzero vectors. -/
theorem compatible_metric_pos {x : E} (hx : x ≠ 0) :
    0 < J.symplecticForm x (J x) := by
  rw [J.symplecticForm_map_right]
  exact real_inner_self_pos.mpr hx

theorem symplecticForm_skew (x y : E) :
    J.symplecticForm x y = -J.symplecticForm y x := by
  simp only [symplecticForm_apply, neg_neg]
  have h := J.inner_map_left x y
  have hc := real_inner_comm (J x) y
  linarith

theorem symplecticForm_isAlt : J.symplecticForm.IsAlt := by
  intro x
  simp

@[simp] theorem symplecticForm_map_map (x y : E) :
    J.symplecticForm (J x) (J y) = J.symplecticForm x y := by
  simp only [symplecticForm_apply, apply_apply, inner_neg_right, neg_neg]
  exact J.inner_map_left x y

/-- The form is genuinely nondegenerate, on both arguments. -/
theorem symplecticForm_nondegenerate : J.symplecticForm.Nondegenerate := by
  constructor
  · intro x hx
    simpa using hx (J x)
  · intro x hx
    have h := hx (J x)
    simp only [symplecticForm_apply, inner_map_map, neg_eq_zero] at h
    exact inner_self_eq_zero.mp h

/-- Symplectic and metric complements agree exactly on J-invariant subspaces. -/
theorem symplectic_orthogonal_eq {A : Submodule ℝ E} (hA : J.IsInvariant A) :
    J.symplecticForm.orthogonal A = Aᗮ := by
  ext x
  constructor
  · intro hx a ha
    have h := hx (J a) (hA a ha)
    simpa using h
  · intro hx a ha
    have h := hx (J a) (hA a ha)
    have hs := J.inner_map_left a x
    change -⟪a,J x⟫ = 0
    linarith

/-- Every invariant subspace is symplectic, including the zero subspace. -/
theorem symplectic_restrict_nondegenerate {A : Submodule ℝ E} (hA : J.IsInvariant A) :
    (J.symplecticForm.restrict A).Nondegenerate := by
  apply J.symplecticForm.nondegenerate_restrict_of_disjoint_orthogonal
  · exact J.symplecticForm_isAlt.isRefl
  · rw [J.symplectic_orthogonal_eq hA]
    exact A.orthogonal_disjoint

/-- The selected plane and its bosonic complement are nondegenerate and form a direct sum. -/
theorem plane_symplectic_split [FiniteDimensional ℝ E] (v : E) :
    (J.symplecticForm.restrict (J.plane v)).Nondegenerate ∧
    (J.symplecticForm.restrict (J.symplecticForm.orthogonal (J.plane v))).Nondegenerate ∧
    IsCompl (J.plane v) (J.symplecticForm.orthogonal (J.plane v)) := by
  rw [J.symplectic_orthogonal_eq (J.plane_invariant v)]
  exact ⟨J.symplectic_restrict_nondegenerate (J.plane_invariant v),
    J.symplectic_restrict_nondegenerate (J.orthogonal_invariant (J.plane_invariant v)),
    (J.plane v).isCompl_orthogonal⟩

/-- The crosswalk in the actual bosonic symplectic form, with C=A^(perp Ω).
No Euclidean-complement assumption on the original physical split is used. -/
theorem symplectic_hull_orthogonal (A : Submodule ℝ E) :
    J.symplecticForm.orthogonal (A ⊔ J.image A) =
      J.symplecticForm.orthogonal A ⊓ J.image (J.symplecticForm.orthogonal A) := by
  ext x
  constructor
  · intro hx
    constructor
    · intro a ha
      exact hx a ((show A ≤ A ⊔ J.image A from le_sup_left) ha)
    · refine ⟨-J x, ?_, by simp⟩
      intro a ha
      have h := hx (J a) ((show J.image A ≤ A ⊔ J.image A from le_sup_right) ⟨a,ha,rfl⟩)
      simpa using h
  · rintro ⟨hx, y, hy, hxy⟩ a ha
    obtain ⟨a₁,ha₁,a₂,ha₂,rfl⟩ := Submodule.mem_sup.mp ha
    rw [map_add, LinearMap.add_apply]
    have h₁ := hx a₁ ha₁
    obtain ⟨b,hb,rfl⟩ := ha₂
    have h₂ : J.symplecticForm (J b) x = 0 := by
      change J y = x at hxy
      rw [← hxy, J.symplecticForm_map_map]
      exact hy b hb
    change J.symplecticForm a₁ x + J.symplecticForm (J b) x = 0
    rw [h₁,h₂,add_zero]

end OrthogonalComplexStructure
end Gaussian.Phase
