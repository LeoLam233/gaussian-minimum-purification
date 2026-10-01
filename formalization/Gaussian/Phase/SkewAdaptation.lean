import Gaussian.Phase.CompatibleGeometry
import Gaussian.Phase.PositiveTools
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Raw finite-dimensional real skew-operator constructions. -/
universe u
noncomputable section
open Module
open scoped RealInnerProductSpace

namespace Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The raw skew-adjoint equation, without invertibility or spectral assumptions. -/
def IsSkew (T : E →ₗ[ℝ] E) : Prop := ∀ x y, ⟪T x,y⟫ = -⟪x,T y⟫

/-- Explicit algebraic witnesses for a skew polar adaptation. These are the
conclusions to be constructed, not a covariance admissibility interface. -/
structure SkewAdaptationData (T : E →ₗ[ℝ] E) where
  J : E →ₗ[ℝ] E
  K : E →ₗ[ℝ] E
  square_neg : ∀ x, J (J x) = -x
  skew : IsSkew J
  positive : K.IsPositive
  factor : ∀ x, T x = J (K x)
  commute : ∀ x, J (K x) = K (J x)

namespace SkewAdaptationData
variable {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)

theorem inner_map_map (x y : E) : ⟪d.J x,d.J y⟫ = ⟪x,y⟫ := by
  rw [d.skew, d.square_neg, inner_neg_right, neg_neg]

/-- The constructed J really is an orthogonal complex structure. -/
def complexStructure : OrthogonalComplexStructure E where
  equiv := LinearIsometryEquiv.ofSurjective
    { toLinearMap := d.J
      norm_map' := fun x => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
          ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, d.inner_map_map] }
    (fun x => ⟨-d.J x, by simp [d.square_neg]⟩)
  square_neg := d.square_neg

theorem norm_J (x : E) : ‖d.J x‖ = ‖x‖ := d.complexStructure.equiv.norm_map x

/-- The amplitude and the raw skew operator have the same pointwise norm. -/
theorem norm_K (x : E) : ‖d.K x‖ = ‖T x‖ := by
  rw [d.factor, d.norm_J]

/-- Raw norm-contractivity of T gives the full operator inequality 0≤K≤I. -/
theorem one_sub_positive (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    (LinearMap.id - d.K).IsPositive := by
  refine ⟨LinearMap.IsSymmetric.id.sub d.positive.isSymmetric, ?_⟩
  intro x
  change 0 ≤ ⟪x-d.K x,x⟫
  rw [inner_sub_left]
  apply sub_nonneg.mpr
  calc
    ⟪d.K x,x⟫ ≤ ‖d.K x‖*‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖*‖x‖ := mul_le_mul_of_nonneg_right (by rw [d.norm_K]; exact hT x) (norm_nonneg x)
    _ = ⟪x,x⟫ := (real_inner_self_eq_norm_mul_norm x).symm

/-- Invertibility is only needed to obtain strict positivity, not adaptation. -/
theorem K_injective (hT : Function.Injective T) : Function.Injective d.K := by
  intro x y hxy
  apply hT
  rw [d.factor,d.factor,hxy]

theorem K_inner_pos (hT : Function.Injective T) {x : E} (hx : x ≠ 0) :
    0 < ⟪d.K x,x⟫ := positive_inner_pos_of_injective d.positive (d.K_injective hT) hx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Orthogonal transport preserves every part of an adaptation. -/
def transport (e : E ≃ₗᵢ[ℝ] F) :
    SkewAdaptationData (e.toLinearEquiv.conj T) where
  J := e.toLinearEquiv.conj d.J
  K := e.toLinearEquiv.conj d.K
  square_neg x := by simp [LinearEquiv.conj_apply, d.square_neg]
  skew x y := by
    change ⟪e (d.J (e.symm x)),y⟫ = -⟪x,e (d.J (e.symm y))⟫
    conv_lhs => rw [← e.apply_symm_apply y]
    conv_rhs => rw [← e.apply_symm_apply x]
    simpa only [e.inner_map_map] using d.skew (e.symm x) (e.symm y)
  positive := by
    constructor
    · intro x y
      change ⟪e (d.K (e.symm x)),y⟫ = ⟪x,e (d.K (e.symm y))⟫
      conv_lhs => rw [← e.apply_symm_apply y]
      conv_rhs => rw [← e.apply_symm_apply x]
      simpa only [e.inner_map_map] using d.positive.isSymmetric (e.symm x) (e.symm y)
    · intro x
      change 0 ≤ ⟪e (d.K (e.symm x)),x⟫
      conv_rhs => rw [← e.apply_symm_apply x]
      simpa only [e.inner_map_map, e.symm_apply_apply] using d.positive.inner_nonneg_left (e.symm x)
  factor x := by simp [LinearEquiv.conj_apply, d.factor]
  commute x := by simp [LinearEquiv.conj_apply, d.commute]

/-- Orthogonal direct sums preserve adaptations, including singular zero blocks. -/
def prod {S : F →ₗ[ℝ] F} (d' : SkewAdaptationData S) :
    SkewAdaptationData ((T.prodMap S).withLpMap 2) where
  J := (d.J.prodMap d'.J).withLpMap 2
  K := (d.K.prodMap d'.K).withLpMap 2
  square_neg x := by
    apply WithLp.ofLp_injective
    ext <;> simp [d.square_neg, d'.square_neg]
  skew x y := by
    change ⟪d.J x.ofLp.1,y.ofLp.1⟫ + ⟪d'.J x.ofLp.2,y.ofLp.2⟫ =
      -(⟪x.ofLp.1,d.J y.ofLp.1⟫ + ⟪x.ofLp.2,d'.J y.ofLp.2⟫)
    rw [d.skew, d'.skew]
    ring
  positive := by
    constructor
    · intro x y
      change ⟪d.K x.ofLp.1,y.ofLp.1⟫ + ⟪d'.K x.ofLp.2,y.ofLp.2⟫ =
        ⟪x.ofLp.1,d.K y.ofLp.1⟫ + ⟪x.ofLp.2,d'.K y.ofLp.2⟫
      rw [d.positive.isSymmetric, d'.positive.isSymmetric]
    · intro x
      exact add_nonneg (d.positive.inner_nonneg_left x.ofLp.1)
        (d'.positive.inner_nonneg_left x.ofLp.2)
  factor x := by
    apply WithLp.ofLp_injective
    ext <;> simp [d.factor, d'.factor]
  commute x := by
    apply WithLp.ofLp_injective
    ext <;> simp [d.commute, d'.commute]

/-- The unique operator on the empty real space has a complete adaptation. -/
def ofSubsingleton [Subsingleton E] (T : E →ₗ[ℝ] E) : SkewAdaptationData T where
  J := 0
  K := 0
  square_neg _ := Subsingleton.elim _ _
  skew _ _ := by simp
  positive := LinearMap.isPositive_zero
  factor _ := Subsingleton.elim _ _
  commute _ := rfl

end SkewAdaptationData

/-- The real plane generated by an orthonormal block pair. -/
def blockPlane (u v : E) : Submodule ℝ E := Submodule.span ℝ ({u,v} : Set E)

/-- Rotation on the selected plane, zero on its orthogonal complement. -/
def blockRotation (u v : E) : E →ₗ[ℝ] E :=
  (innerₗ E u).smulRight v - (innerₗ E v).smulRight u

@[simp] theorem blockRotation_apply (u v x : E) :
    blockRotation u v x = ⟪u,x⟫ • v - ⟪v,x⟫ • u := rfl

theorem blockRotation_skew (u v : E) : IsSkew (blockRotation u v) := by
  intro x y
  simp only [blockRotation_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm x v, real_inner_comm x u]
  ring

theorem blockRotation_mem (u v x : E) : blockRotation u v x ∈ blockPlane u v := by
  apply Submodule.sub_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem blockPlane_reconstruct {u v x : E} (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1)
    (huv : ⟪u,v⟫ = 0) (hx : x ∈ blockPlane u v) :
    x = ⟪u,x⟫ • u + ⟪v,x⟫ • v := by
  have hvu : ⟪v,u⟫ = 0 := by rwa [real_inner_comm]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · simp only [hu,hvu,one_smul,zero_smul,add_zero]
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      simp only [hv,huv,one_smul,zero_smul,zero_add]
  | zero => simp
  | add x y hx hy hx' hy' =>
    conv_lhs => rw [hx',hy']
    rw [inner_add_right, inner_add_right, add_smul, add_smul]
    abel
  | smul r x hx hx' =>
    conv_lhs => rw [hx', smul_add, smul_smul, smul_smul]
    rw [inner_smul_right, inner_smul_right]

theorem finrank_blockPlane {u v : E} (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1)
    (huv : ⟪u,v⟫ = 0) : finrank ℝ (blockPlane u v) = 2 := by
  have hli : LinearIndependent ℝ ![u,v] := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      change v = 0 at h
      rw [h,inner_zero_left] at hv
      norm_num at hv
    · intro r hr
      have hh := congrArg (fun x : E => ⟪u,x⟫) hr
      change ⟪u,r • v⟫ = ⟪u,u⟫ at hh
      rw [inner_smul_right,huv,hu,mul_zero] at hh
      norm_num at hh
  have hr : Set.range ![u,v] = ({u,v} : Set E) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hd := finrank_span_eq_card hli
  rw [hr] at hd
  exact hd

/-- The block equations force the whole spanned plane to be invariant. -/
theorem blockPlane_invariant {T : E →ₗ[ℝ] E} {u v : E} {r : ℝ}
    (hTu : T u = r • v) (hTv : T v = -r • u) :
    ∀ x ∈ blockPlane u v, T x ∈ blockPlane u v := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [hTu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      rw [hTv]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | zero => simp
  | add x y hx hy hx' hy' => simpa using Submodule.add_mem _ hx' hy'
  | smul r x hx hx' => simpa using Submodule.smul_mem _ r hx'

/-- Construct the full adaptation on a two-dimensional block, including r=0. -/
def blockAdaptation {T : E →ₗ[ℝ] E} {u v : E} {r : ℝ}
    (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1) (huv : ⟪u,v⟫ = 0) (hr : 0 ≤ r)
    (hTu : T u = r • v) (hTv : T v = -r • u) :
    SkewAdaptationData (T.restrict (blockPlane_invariant hTu hTv)) := by
  let P := blockPlane u v
  let R : P →ₗ[ℝ] P := (blockRotation u v).restrict (fun x _ => blockRotation_mem u v x)
  have hvu : ⟪v,u⟫ = 0 := by rwa [real_inner_comm]
  refine { J := R
           K := r • LinearMap.id
           square_neg := ?_
           skew := ?_
           positive := LinearMap.isPositive_id.smul_of_nonneg hr
           factor := ?_
           commute := ?_ }
  · intro x
    apply Subtype.ext
    change blockRotation u v (blockRotation u v x) = -(x : E)
    simp only [blockRotation_apply, inner_sub_right, inner_smul_right, hu,hv,huv,hvu,
      mul_zero, mul_one, sub_zero, zero_sub, neg_smul]
    conv_rhs => rw [blockPlane_reconstruct hu hv huv x.property]
    abel
  · intro x y
    exact blockRotation_skew u v x y
  · intro x
    apply Subtype.ext
    change T x = blockRotation u v (r • (x : E))
    rw [map_smul]
    conv_lhs => rw [blockPlane_reconstruct hu hv huv x.property]
    rw [map_add, map_smul, map_smul, hTu,hTv,blockRotation_apply, smul_sub,
      smul_smul, smul_smul, smul_smul,smul_smul]
    simp only [mul_neg, neg_smul, sub_eq_add_neg]
    simp only [mul_comm]
  · intro x
    exact R.map_smul r x


namespace IsSkew
variable {T : E →ₗ[ℝ] E} (hT : IsSkew T)
include hT

theorem inner_self (x : E) : ⟪x,T x⟫ = 0 := by
  have h := hT x x
  have hc := real_inner_comm (T x) x
  linarith

/-- Minus the square is a genuine positive self-adjoint operator, even when singular. -/
theorem neg_square_positive : (-(T * T)).IsPositive := by
  constructor
  · intro x y
    change ⟪-T (T x),y⟫ = ⟪x,-T (T y)⟫
    simp only [inner_neg_left, inner_neg_right]
    rw [hT (T x) y, ← hT x (T y)]
    simp
  · intro x
    change 0 ≤ ⟪-T (T x),x⟫
    rw [inner_neg_left, hT (T x) x, neg_neg]
    exact real_inner_self_nonneg

/-- Skew-adjointness ensures invariant subspaces have invariant orthogonal complements. -/
theorem orthogonal_invariant {A : Submodule ℝ E}
    (hA : ∀ x ∈ A, T x ∈ A) : ∀ x ∈ Aᗮ, T x ∈ Aᗮ := by
  intro x hx a ha
  have h := hx (T a) (hA a ha)
  have hs := hT a x
  linarith

/-- Restriction preserves the raw skew-adjoint equation. -/
theorem restrict {A : Submodule ℝ E} (hA : ∀ x ∈ A, T x ∈ A) :
    IsSkew (T.restrict hA) := by
  intro x y
  exact hT x y

/-- A nonzero real skew operator has an orthonormal invariant two-plane with
strictly positive block parameter. This is extracted from the real spectral theorem
for -T² and does not invoke a skew normal-form hypothesis. -/
theorem exists_positive_block [FiniteDimensional ℝ E] (hT0 : T ≠ 0) :
    ∃ (u v : E) (r : ℝ), 0 < r ∧ ⟪u,u⟫ = 1 ∧ ⟪v,v⟫ = 1 ∧ ⟪u,v⟫ = 0 ∧
      T u = r • v ∧ T v = -r • u := by
  let S := -(T * T)
  have hS : S.IsPositive := hT.neg_square_positive
  let b := hS.isSymmetric.eigenvectorBasis rfl
  obtain ⟨i,hi⟩ : ∃ i, T (b i) ≠ 0 := by
    by_contra! h
    apply hT0
    apply b.toBasis.ext
    intro i
    simpa using h i
  let u := b i
  let a := hS.isSymmetric.eigenvalues rfl i
  have huu : ⟪u,u⟫ = 1 := by simp [u, b]
  have he : -T (T u) = a • u := by
    exact hS.isSymmetric.apply_eigenvectorBasis rfl i
  have haa : ⟪T u,T u⟫ = a := by
    have h := congrArg (fun x : E => ⟪x,u⟫) he
    simp only [inner_neg_left, hT (T u) u, neg_neg, inner_smul_left,
      RCLike.conj_to_real, huu, mul_one] at h
    exact h
  have ha : 0 < a := by
    rw [← haa]
    exact real_inner_self_pos.mpr hi
  let r := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr2 : r*r = a := Real.mul_self_sqrt ha.le
  let v := r⁻¹ • T u
  refine ⟨u,v,r,hr,huu,?_,?_,?_,?_⟩
  · dsimp [v]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real, haa]
    rw [← hr2]
    field_simp
  · dsimp [v]
    simp only [inner_smul_right, hT.inner_self, mul_zero]
  · dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
  · dsimp [v]
    rw [map_smul]
    have htt : T (T u) = -a • u := by
      have hh := congrArg Neg.neg he
      simpa using hh
    rw [htt, smul_smul]
    congr 1
    rw [← hr2]
    field_simp

/-- Every nonempty even-dimensional skew operator has a block. The zero
operator receives an arbitrary orthonormal zero block rather than being inverted. -/
theorem exists_nonneg_block [FiniteDimensional ℝ E] (hd : 2 ≤ finrank ℝ E) :
    ∃ (u v : E) (r : ℝ), 0 ≤ r ∧ ⟪u,u⟫ = 1 ∧ ⟪v,v⟫ = 1 ∧ ⟪u,v⟫ = 0 ∧
      T u = r • v ∧ T v = -r • u := by
  by_cases hT0 : T = 0
  · let b := stdOrthonormalBasis ℝ E
    let i : Fin (finrank ℝ E) := ⟨0,by omega⟩
    let j : Fin (finrank ℝ E) := ⟨1,by omega⟩
    have hij : i ≠ j := by simp [i,j]
    refine ⟨b i,b j,0,le_rfl,?_,?_,?_,?_,?_⟩
    · simp only [b.inner_eq_ite, ite_true]
    · simp only [b.inner_eq_ite, ite_true]
    · simp only [b.inner_eq_ite, ite_eq_right_iff]
      exact fun h => (hij h).elim
    · simp [hT0]
    · simp [hT0]
  · obtain ⟨u,v,r,hr,hu,hv,huv,hTu,hTv⟩ := hT.exists_positive_block hT0
    exact ⟨u,v,r,hr.le,hu,hv,huv,hTu,hTv⟩

end IsSkew

namespace SkewAdaptationData
variable {T : E →ₗ[ℝ] E} [FiniteDimensional ℝ E]

/-- Assemble independently constructed adaptations on an invariant subspace
and its orthogonal complement. -/
def glue (hT : IsSkew T) (P : Submodule ℝ E) (hP : ∀ x ∈ P, T x ∈ P)
    (dP : SkewAdaptationData (T.restrict hP))
    (dQ : SkewAdaptationData (T.restrict (hT.orthogonal_invariant hP))) :
    SkewAdaptationData T := by
  let e := P.orthogonalDecomposition.symm
  have he : e.toLinearEquiv.conj
      (((T.restrict hP).prodMap (T.restrict (hT.orthogonal_invariant hP))).withLpMap 2) = T := by
    ext x
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    change P.orthogonalDecomposition.symm
      ((((T.restrict hP).prodMap (T.restrict (hT.orthogonal_invariant hP))).withLpMap 2)
        (P.orthogonalDecomposition x)) = T x
    rw [Submodule.orthogonalDecomposition_symm_apply, Submodule.orthogonalDecomposition_apply]
    change T (P.orthogonalProjectionOnto x) + T (Pᗮ.orthogonalProjectionOnto x) = T x
    rw [← map_add]
    congr 1
    exact Submodule.starProjection_add_starProjection_orthogonal x
  exact he ▸ (dP.prod dQ).transport e
end SkewAdaptationData

/-- Construction by real dimension induction; neither a skew normal form nor
invertibility is an input. Even-dimensional zero kernels are handled by zero blocks. -/
theorem exists_skewAdaptation_dim : ∀ n : ℕ, ∀ (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    finrank ℝ E = 2*n → ∀ (T : E →ₗ[ℝ] E), IsSkew T → Nonempty (SkewAdaptationData T) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ hd T hT
    haveI : Subsingleton E := Module.finrank_zero_iff.mp (by simpa using hd)
    exact ⟨SkewAdaptationData.ofSubsingleton T⟩
  | succ n ih =>
    intro E _ _ _ hd T hT
    obtain ⟨u,v,r,hr,hu,hv,huv,hTu,hTv⟩ := hT.exists_nonneg_block (by omega)
    let P := blockPlane u v
    have hP : ∀ x ∈ P, T x ∈ P := blockPlane_invariant hTu hTv
    have hQ := hT.orthogonal_invariant hP
    have hdimP : finrank ℝ P = 2 := finrank_blockPlane hu hv huv
    have hdimQ : finrank ℝ ↥Pᗮ = 2*n := by
      have hdim := P.finrank_add_finrank_orthogonal
      omega
    obtain ⟨dQ⟩ := ih Pᗮ hdimQ (T.restrict hQ) (hT.restrict hQ)
    exact ⟨SkewAdaptationData.glue hT P hP (blockAdaptation hu hv huv hr hTu hTv) dQ⟩

/-- Every even finite-dimensional real skew operator admits an orthogonal
complex structure and a commuting positive symmetric amplitude, including T=0. -/
theorem exists_skewAdaptation [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E)
    (hT : IsSkew T) (hEven : Even (finrank ℝ E)) : Nonempty (SkewAdaptationData T) := by
  obtain ⟨n,hn⟩ := hEven
  exact exists_skewAdaptation_dim n E (by omega) T hT

/-- The explicit raw-data conclusion in geometric language. -/
theorem exists_orthogonalComplexStructure_positive [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : IsSkew T) (hEven : Even (finrank ℝ E)) :
    ∃ (J : OrthogonalComplexStructure E) (K : E →ₗ[ℝ] E), K.IsPositive ∧
      (∀ x, T x = J (K x)) ∧ (∀ x, J (K x) = K (J x)) := by
  obtain ⟨d⟩ := exists_skewAdaptation T hT hEven
  exact ⟨d.complexStructure,d.K,d.positive,d.factor,d.commute⟩

/-- Fermionic covariance-level adaptation under the actual Euclidean contraction
condition. Zero covariance modes and repeated singular values are included. -/
theorem exists_orthogonalComplexStructure_contraction [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : IsSkew T) (hEven : Even (finrank ℝ E))
    (hBound : ∀ x, ‖T x‖ ≤ ‖x‖) :
    ∃ (J : OrthogonalComplexStructure E) (K : E →ₗ[ℝ] E), K.IsPositive ∧
      (LinearMap.id-K).IsPositive ∧ (∀ x, T x = J (K x)) ∧
      (∀ x, J (K x) = K (J x)) := by
  obtain ⟨d⟩ := exists_skewAdaptation T hT hEven
  exact ⟨d.complexStructure,d.K,d.positive,d.one_sub_positive hBound,d.factor,d.commute⟩

end Gaussian.Phase
