import Gaussian.Phase.BosonicSpectrum

/-! Genuine paired orthonormal eigenframes. The construction uses a real
eigenvector, its J partner, and the invariant orthogonal complement. -/
universe u
noncomputable section
open Module Module.End
open scoped RealInnerProductSpace
namespace Gaussian.Phase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A complete paired eigenframe, counting each real two-plane once. -/
structure PairedEigenframe (J : OrthogonalComplexStructure E) (K : E →ₗ[ℝ] E) (n : ℕ) where
  basis : OrthonormalBasis (Fin n × Fin 2) ℝ E
  value : Fin n → ℝ
  partner : ∀ i, J (basis (i,0)) = basis (i,1)
  eigen : ∀ i k, K (basis (i,k)) = value i • basis (i,k)

namespace PairedEigenframe
variable {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)
include b

theorem partner_second (i : Fin n) : J (b.basis (i,1)) = -b.basis (i,0) := by
  rw [← b.partner,J.square_neg]

theorem finrank_eq : finrank ℝ E = 2*n := by
  rw [Module.finrank_eq_card_basis b.basis.toBasis,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
  omega
end PairedEigenframe

/-- A pair of unit orthogonal vectors is an actual orthonormal basis of its plane. -/
def pairBasis {u v : E} (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1) (huv : ⟪u,v⟫ = 0) :
    OrthonormalBasis (Fin 2) ℝ (blockPlane u v) := by
  let p : Fin 2 → blockPlane u v :=
    ![⟨u,Submodule.subset_span (by simp)⟩,⟨v,Submodule.subset_span (by simp)⟩]
  have hvu : ⟪v,u⟫ = 0 := by rwa [real_inner_comm]
  have hp : Orthonormal ℝ p := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hu
    · exact huv
    · exact hvu
    · exact hv
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range p) := by
    apply (Submodule.eq_top_of_finrank_eq _).ge
    rw [finrank_span_eq_card hp.linearIndependent,finrank_blockPlane hu hv huv,Fintype.card_fin]
  exact OrthonormalBasis.mk hp hsp

/-- The coordinate identification that adds a new first pair. -/
def pairedConsEquiv (n : ℕ) : (Fin 2 ⊕ (Fin n × Fin 2)) ≃ (Fin (n+1) × Fin 2) where
  toFun := fun s => match s with
    | .inl k => (0,k)
    | .inr (i,k) => (i.succ,k)
  invFun := fun (i,k) => Fin.cases (.inl k) (fun j => .inr (j,k)) i
  left_inv s := by cases s with | inl k => rfl | inr ik => rfl
  right_inv ik := by rcases ik with ⟨i,k⟩; induction i using Fin.cases <;> rfl

@[simp] theorem pairedConsEquiv_symm_zero (n : ℕ) (k : Fin 2) :
    (pairedConsEquiv n).symm (0,k) = Sum.inl k := rfl

@[simp] theorem pairedConsEquiv_symm_succ {n : ℕ} (i : Fin n) (k : Fin 2) :
    (pairedConsEquiv n).symm (i.succ,k) = Sum.inr (i,k) := rfl

@[simp] theorem pairBasis_zero {u v : E} (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1)
    (huv : ⟪u,v⟫ = 0) : (pairBasis hu hv huv 0 : E) = u := by simp [pairBasis]

@[simp] theorem pairBasis_one {u v : E} (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1)
    (huv : ⟪u,v⟫ = 0) : (pairBasis hu hv huv 1 : E) = v := by simp [pairBasis]

/-- Add the first pair to a paired orthonormal basis of its orthogonal complement. -/
def gluePairBasis {n : ℕ} (P : Submodule ℝ E)
    (p : OrthonormalBasis (Fin 2) ℝ P) (q : OrthonormalBasis (Fin n × Fin 2) ℝ Pᗮ) :
    OrthonormalBasis (Fin (n+1) × Fin 2) ℝ E :=
  ((p.prod q).map P.orthogonalDecomposition.symm).reindex (pairedConsEquiv n)

@[simp] theorem gluePairBasis_zero {n : ℕ} (P : Submodule ℝ E)
    (p : OrthonormalBasis (Fin 2) ℝ P) (q : OrthonormalBasis (Fin n × Fin 2) ℝ Pᗮ)
    (k : Fin 2) : gluePairBasis P p q (0,k) = (p k : E) := by
  simp [gluePairBasis,OrthonormalBasis.prod_apply]

@[simp] theorem gluePairBasis_succ {n : ℕ} (P : Submodule ℝ E)
    (p : OrthonormalBasis (Fin 2) ℝ P) (q : OrthonormalBasis (Fin n × Fin 2) ℝ Pᗮ)
    (i : Fin n) (k : Fin 2) : gluePairBasis P p q (i.succ,k) = (q (i,k) : E) := by
  simp [gluePairBasis,OrthonormalBasis.prod_apply]

/-- Full paired eigenframe existence by induction, valid with repeated eigenvalues
and arbitrary eigenspace multiplicities. No simple-spectrum or invertibility input. -/
theorem exists_pairedEigenframe_dim : ∀ n : ℕ, ∀ (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    finrank ℝ E = 2*n → ∀ (J : OrthogonalComplexStructure E) (K : E →ₗ[ℝ] E),
      K.IsSymmetric → (∀ x, J (K x) = K (J x)) → Nonempty (PairedEigenframe J K n) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ hd J K hKs hK
    haveI : Subsingleton E := Module.finrank_zero_iff.mp (by simpa using hd)
    let f : Fin 0 × Fin 2 → E := fun i => Fin.elim0 i.1
    have hf : Orthonormal ℝ f := by rw [orthonormal_iff_ite]; intro i; exact Fin.elim0 i.1
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range f) := by
      intro x _
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      exact Submodule.zero_mem _
    exact ⟨{ basis := OrthonormalBasis.mk hf hsp
             value := Fin.elim0
             partner := fun i => Fin.elim0 i
             eigen := fun i => Fin.elim0 i }⟩
  | succ n ih =>
    intro E _ _ _ hd J K hKs hK
    let z : Fin (2*(n+1)) := ⟨0,by omega⟩
    let u := hKs.eigenvectorBasis hd z
    let r := hKs.eigenvalues hd z
    have hu : ⟪u,u⟫ = 1 := by simp [u]
    have hv : ⟪J u,J u⟫ = 1 := by rw [J.inner_map_map,hu]
    have huv : ⟪u,J u⟫ = 0 := J.inner_self_map u
    have hKu : K u = r • u := hKs.apply_eigenvectorBasis hd z
    have hKv : K (J u) = r • J u := by rw [← hK,hKu,J.apply_smul]
    let P := blockPlane u (J u)
    have hPe : P ≤ eigenspace K r := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact mem_eigenspace_iff.mpr hKu
      · have hx' := Set.mem_singleton_iff.mp hx
        subst x
        exact mem_eigenspace_iff.mpr hKv
    have hKP : ∀ x ∈ P, K x ∈ P := by
      intro x hx
      rw [mem_eigenspace_iff.mp (hPe hx)]
      exact P.smul_mem r hx
    have hKQ : ∀ x ∈ Pᗮ, K x ∈ Pᗮ := by
      intro x hx a ha
      rw [← hKs a x]
      exact hx (K a) (hKP a ha)
    have hJP : J.IsInvariant P := J.plane_invariant u
    have hJQ := J.orthogonal_invariant hJP
    let JQ := J.restrict Pᗮ hJQ
    let KQ := K.restrict hKQ
    have hQsym : KQ.IsSymmetric := hKs.restrict_invariant hKQ
    have hQcomm : ∀ x, JQ (KQ x) = KQ (JQ x) := by
      intro x
      apply Subtype.ext
      exact hK x
    have hdimP : finrank ℝ P = 2 := finrank_blockPlane hu hv huv
    have hdimQ : finrank ℝ ↥Pᗮ = 2*n := by
      have hh := P.finrank_add_finrank_orthogonal
      omega
    obtain ⟨q⟩ := ih Pᗮ hdimQ JQ KQ hQsym hQcomm
    let p := pairBasis hu hv huv
    have hp0 : (p 0 : E) = u := pairBasis_zero hu hv huv
    have hp1 : (p 1 : E) = J u := pairBasis_one hu hv huv
    refine ⟨{ basis := gluePairBasis P p q.basis
              value := Fin.cases r q.value
              partner := ?_
              eigen := ?_ }⟩
    · intro i
      induction i using Fin.cases with
      | zero => rw [gluePairBasis_zero,gluePairBasis_zero,hp0,hp1]
      | succ i =>
        simp only [gluePairBasis_succ]
        exact congrArg (fun x : Pᗮ => (x : E)) (q.partner i)
    · intro i k
      induction i using Fin.cases with
      | zero =>
        simp only [gluePairBasis_zero,Fin.cases_zero]
        fin_cases k
        · change K (p 0 : E) = r • (p 0 : E)
          rw [hp0]
          exact hKu
        · change K (p 1 : E) = r • (p 1 : E)
          rw [hp1]
          exact hKv
      | succ i =>
        simp only [gluePairBasis_succ,Fin.cases_succ]
        exact congrArg (fun x : Pᗮ => (x : E)) (q.eigen i k)

/-- Canonical block-diagonal alternating matrix, in pair order (q,p). -/
def canonicalModeMatrix (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  fun i j => if i.1 = j.1 then (!![0,1; -1,0] : Matrix (Fin 2) (Fin 2) ℝ) i.2 j.2 else 0

namespace PairedEigenframe
variable {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- The frame is genuinely canonical for the induced symplectic form. -/
theorem symplectic_matrix (i j : Fin n × Fin 2) :
    J.symplecticForm (b.basis i) (b.basis j) = canonicalModeMatrix n i j := by
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,l⟩
  fin_cases k <;> fin_cases l
  · change J.symplecticForm (b.basis (i,0)) (b.basis (j,0)) = _
    simp [OrthogonalComplexStructure.symplecticForm_apply,b.partner,b.basis.inner_eq_ite,
      canonicalModeMatrix]
  · change J.symplecticForm (b.basis (i,0)) (b.basis (j,1)) = _
    simp [OrthogonalComplexStructure.symplecticForm_apply,b.partner_second,b.basis.inner_eq_ite,
      canonicalModeMatrix]
  · change J.symplecticForm (b.basis (i,1)) (b.basis (j,0)) = _
    simp [OrthogonalComplexStructure.symplecticForm_apply,b.partner,b.basis.inner_eq_ite,
      canonicalModeMatrix]
    split_ifs <;> simp
  · change J.symplecticForm (b.basis (i,1)) (b.basis (j,1)) = _
    simp [OrthogonalComplexStructure.symplecticForm_apply,b.partner_second,b.basis.inner_eq_ite,
      canonicalModeMatrix]

/-- The quadratic form of K is diagonal with each mode parameter repeated twice. -/
theorem amplitude_matrix (i j : Fin n × Fin 2) :
    ⟪b.basis i,K (b.basis j)⟫ = if i=j then b.value i.1 else 0 := by
  rw [b.eigen j.1 j.2,inner_smul_right,b.basis.inner_eq_ite]
  split_ifs with h
  · have hij : i = j := h
    subst j
    simp
  · simp

/-- Lower bounds on the amplitude yield the same lower bounds on every pair parameter. -/
theorem value_ge (c : ℝ) (hLower : ∀ x, c*⟪x,x⟫ ≤ ⟪x,K x⟫) (i : Fin n) :
    c ≤ b.value i := by
  have h := hLower (b.basis (i,0))
  rw [b.amplitude_matrix,b.basis.inner_eq_ite] at h
  simpa using h

end PairedEigenframe

/-- Any finite orthonormal eigenframe gives the same multiplicity-counted
spectral sum as the library's independent sorted spectrum. -/
theorem spectral_sum_eq_eigenframe_sum {ι : Type*} [Fintype ι]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {m : ℕ} (hm : finrank ℝ E = m)
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (he : ∀ i, T (b i) = a i • b i) (f : ℝ → ℝ) :
    (∑ i : Fin m, f (hT.eigenvalues hm i)) = ∑ i : ι, f (a i) := by
  classical
  have hmtrx : T.toMatrix b.toBasis b.toBasis = Matrix.diagonal a := by
    ext i j
    simp only [LinearMap.toMatrix_apply,he,map_smul,OrthonormalBasis.coe_toBasis,
      Finsupp.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hr : T.charpoly.roots = Multiset.map a Finset.univ.val := by
    rw [← T.charpoly_toMatrix b.toBasis,hmtrx,Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero])]
    simp
  have hs : T.charpoly.roots = Multiset.map (hT.eigenvalues hm) Finset.univ.val := by
    simpa using hT.roots_charpoly_eq_eigenvalues hm
  have h := congrArg (fun s : Multiset ℝ => (s.map f).sum) (hs.symm.trans hr)
  simpa only [Multiset.map_map,Function.comp_def,← Finset.sum_eq_multiset_sum] using h

/-- The factor 1/2 on the doubled real spectrum equals the actual once-per-pair
sum, with a proved paired basis rather than an assumed mode-count interface. -/
theorem paired_half_spectral_sum {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E}
    {n : ℕ} (b : PairedEigenframe J K n) (hK : K.IsSymmetric) (f : ℝ → ℝ) :
    (1/2:ℝ) * (∑ i : Fin (2*n), f (hK.eigenvalues b.finrank_eq i)) =
      ∑ i : Fin n, f (b.value i) := by
  rw [spectral_sum_eq_eigenframe_sum hK b.finrank_eq b.basis (fun i => b.value i.1)
    (fun i => b.eigen i.1 i.2) f]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,Finset.sum_add_distrib]
  ring

end Gaussian.Phase
