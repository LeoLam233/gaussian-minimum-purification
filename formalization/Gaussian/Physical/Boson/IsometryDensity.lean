import Gaussian.Physical.Boson.VectorFamilyMatrix
import Gaussian.Physical.Boson.VectorFamilyExpectation
import Gaussian.Analysis.ChosenHilbertBasis

/-! Actual transport of positive trace-class normal densities across Hilbert-space
isometries. The matrix conjugation formula is proved from convergent vector families. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open ProbabilisticTheory Gaussian.Analysis
open scoped InnerProductSpace
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometry_vectorFamily_hasSum (U : H ≃ₗᵢ[ℂ] K) {ι : Type*} (v : ι → H)
    (hv : HasSum (fun i => ‖v i‖^2) 1) : HasSum (fun i => ‖U (v i)‖^2) 1 := by
  simpa only [U.norm_map] using hv

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
def NormalDensity.mapHilbert (ρ : NormalDensity H) (U : H ≃ₗᵢ[ℂ] K) : NormalDensity K :=
  normalVectorFamily (fun i => U ((CFC.sqrt ρ.operator.1) (chosenHilbertBasis H i)))
    (isometry_vectorFamily_hasSum U _ (ρ.sqrt_vectors_hasSum (chosenHilbertBasis H)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem NormalDensity.mapHilbert_operator (ρ : NormalDensity H) (U : H ≃ₗᵢ[ℂ] K) :
    (ρ.mapHilbert U).operator.1=U.conjStarAlgEquiv ρ.operator.1 := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have h1 (v : H) : ⟪x,U v⟫_ℂ=⟪U.symm x,v⟫_ℂ := by
    simpa only [U.apply_symm_apply] using (U.inner_map_map (U.symm x) v)
  have h2 (v : H) : ⟪U v,y⟫_ℂ=⟪v,U.symm y⟫_ℂ := by
    simpa only [U.apply_symm_apply] using (U.inner_map_map v (U.symm y))
  have hm := normalVectorFamily_matrix_hasSum
    (fun i => U ((CFC.sqrt ρ.operator.1) (chosenHilbertBasis H i)))
    (isometry_vectorFamily_hasSum U _ (ρ.sqrt_vectors_hasSum (chosenHilbertBasis H))) x y
  have hs := ρ.sqrt_matrix_hasSum (chosenHilbertBasis H) (U.symm x) (U.symm y)
  simp only [h1,h2] at hm
  exact (hm.unique hs).trans (h1 (ρ.operator.1 (U.symm y))).symm

@[simp] theorem NormalDensity.mapHilbert_symm (ρ : NormalDensity H) (U : H ≃ₗᵢ[ℂ] K) :
    (ρ.mapHilbert U).mapHilbert U.symm=ρ := by
  apply NormalDensity.ext
  apply Subtype.ext
  rw [NormalDensity.mapHilbert_operator,NormalDensity.mapHilbert_operator]
  ext x
  simp

theorem vectorDensity_mapHilbert (x : H) (hx : ‖x‖=1) (U : H ≃ₗᵢ[ℂ] K) :
    (vectorDensity x hx).mapHilbert U=vectorDensity (U x) ((U.norm_map x).trans hx) := by
  apply NormalDensity.ext
  apply Subtype.ext
  rw [NormalDensity.mapHilbert_operator]
  ext y
  change U (InnerProductSpace.rankOne ℂ x x (U.symm y))=InnerProductSpace.rankOne ℂ (U x) (U x) y
  rw [InnerProductSpace.rankOne_apply,InnerProductSpace.rankOne_apply,map_smul]
  congr 1
  simpa only [U.apply_symm_apply] using (U.inner_map_map x (U.symm y)).symm

theorem NormalDensity.IsPure.mapHilbert {ρ : NormalDensity H} (hρ : ρ.IsPure)
    (U : H ≃ₗᵢ[ℂ] K) : (ρ.mapHilbert U).IsPure := by
  obtain ⟨x,hx,rfl⟩ := hρ
  rw [vectorDensity_mapHilbert]
  exact vectorDensity_isPure _ _

theorem NormalDensity.mapHilbert_isPure_iff (ρ : NormalDensity H) (U : H ≃ₗᵢ[ℂ] K) :
    (ρ.mapHilbert U).IsPure ↔ ρ.IsPure := by
  constructor
  · intro h
    simpa using h.mapHilbert U.symm
  · exact fun h => h.mapHilbert U

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem NormalDensity.expect_mapHilbert (ρ : NormalDensity H) (U : H ≃ₗᵢ[ℂ] K)
    (A : K →L[ℂ] K) :
    (ρ.mapHilbert U).expect A=ρ.expect (U.symm.conjStarAlgEquiv A) := by
  have hm := normalVectorFamily_expect_hasSum
    (fun i => U ((CFC.sqrt ρ.operator.1) (chosenHilbertBasis H i)))
    (isometry_vectorFamily_hasSum U _ (ρ.sqrt_vectors_hasSum (chosenHilbertBasis H))) A
  have h (v : H) : ⟪U v,A (U v)⟫_ℂ=⟪v,(U.symm.conjStarAlgEquiv A) v⟫_ℂ := by
    change ⟪U v,A (U v)⟫_ℂ=⟪v,U.symm (A (U v))⟫_ℂ
    simpa only [U.apply_symm_apply] using U.inner_map_map v (U.symm (A (U v)))
  simp only [h] at hm
  exact hm.unique (ρ.sqrt_expect_hasSum (chosenHilbertBasis H) (U.symm.conjStarAlgEquiv A))

end Gaussian.Physical.Boson
