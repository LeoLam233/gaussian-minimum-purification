import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin

/-! Real self-adjoint compression, using the actual descending spectral list.
No simplicity assumption is made on eigenvalues. The real list retains multiplicities. -/
noncomputable section
open scoped RealInnerProductSpace
open Module
namespace Gaussian.Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Span of the specified members of an orthonormal basis. -/
def spectralSpan (b : OrthonormalBasis ι ℝ E) (s : Set ι) : Submodule ℝ E :=
  Submodule.span ℝ (b '' s)

theorem finrank_spectralSpan (b : OrthonormalBasis ι ℝ E) (s : Set ι) :
    finrank ℝ (spectralSpan b s) = Nat.card s := by
  classical
  have hr : Set.range (fun i : s => b i) = b '' s := by ext; simp
  rw [spectralSpan, ← hr]
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.toBasis.linearIndependent.comp _ Subtype.val_injective)

theorem repr_zero_of_mem_spectralSpan (b : OrthonormalBasis ι ℝ E)
    (s : Set ι) {x : E} (hx : x ∈ spectralSpan b s) {i : ι} (hi : i ∉ s) :
    b.repr x i = 0 := by
  classical
  have hs := b.toBasis.repr_support_subset_of_mem_span s hx
  have hni : i ∉ (b.toBasis.repr x).support := fun h => hi (hs h)
  simpa using Finsupp.notMem_support_iff.mp hni

theorem exists_nonzero_intersection [FiniteDimensional ℝ E]
    (A B : Submodule ℝ E) (h : finrank ℝ E < finrank ℝ A + finrank ℝ B) :
    ∃ x : E, x ∈ A ∧ x ∈ B ∧ x ≠ 0 := by
  have he := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hu := Submodule.finrank_le (A ⊔ B)
  have hn : A ⊓ B ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at he
    omega
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hn
  exact ⟨x,hx.1,hx.2,hx0⟩

variable [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}

/-- Rayleigh numerator in the spectral basis, with real multiplicities. -/
theorem rayleigh_sum (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    ⟪x,T x⟫ = ∑ i : Fin n, hT.eigenvalues hn i *
      ((hT.eigenvectorBasis hn).repr x i)^2 := by
  let b := hT.eigenvectorBasis hn
  rw [← b.sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  have h₁ : ⟪x,b i⟫ = b.repr x i := by
    rw [b.repr_apply_apply]
    exact real_inner_comm _ _
  have h₂ : ⟪b i,T x⟫ = b.repr (T x) i := (b.repr_apply_apply _ _).symm
  rw [h₁,h₂]
  change b.repr x i * (hT.eigenvectorBasis hn).repr (T x) i = _
  rw [hT.eigenvectorBasis_apply_self_apply hn x i]
  simp only [b, RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem spectral_norm_sq (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, (b.repr x i)^2 = ‖x‖^2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right x

/-- A Rayleigh upper bound from the support of the spectral coordinates. -/
theorem rayleigh_le_of_support (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n)
    (s : Set (Fin n)) (c : ℝ) (hs : ∀ i ∈ s, hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ spectralSpan (hT.eigenvectorBasis hn) s) :
    ⟪x,T x⟫ ≤ c * ‖x‖^2 := by
  rw [rayleigh_sum hT hn, ← spectral_norm_sq (hT.eigenvectorBasis hn), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hs i hi) (sq_nonneg _)
  · rw [repr_zero_of_mem_spectralSpan _ s hx hi]
    simp

theorem rayleigh_ge_of_support (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n)
    (s : Set (Fin n)) (c : ℝ) (hs : ∀ i ∈ s, c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ spectralSpan (hT.eigenvectorBasis hn) s) :
    c * ‖x‖^2 ≤ ⟪x,T x⟫ := by
  rw [rayleigh_sum hT hn, ← spectral_norm_sq (hT.eigenvectorBasis hn), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hs i hi) (sq_nonneg _)
  · rw [repr_zero_of_mem_spectralSpan _ s hx hi]
    simp

/-- The genuine orthogonal compression of an operator to a coefficient subspace. -/
def compression (T : E →ₗ[ℝ] E) (U : Submodule ℝ E) : U →ₗ[ℝ] U :=
  U.orthogonalProjectionOnto.toLinearMap.comp (T.comp U.subtype)

@[simp] theorem inner_compression (U : Submodule ℝ E) (x y : U) :
    ⟪x,compression T U y⟫ = ⟪(x : E),T (y : E)⟫ := by
  exact U.inner_orthogonalProjectionOnto_eq_of_mem_left x (T y)

theorem compression_symmetric (hT : T.IsSymmetric) (U : Submodule ℝ E) :
    (compression T U).IsSymmetric := by
  intro x y
  calc
    ⟪compression T U x,y⟫ = ⟪y,compression T U x⟫ := real_inner_comm _ _
    _ = ⟪(y : E),T (x : E)⟫ := inner_compression U y x
    _ = ⟪T (x : E),(y : E)⟫ := real_inner_comm _ _
    _ = ⟪(x : E),T (y : E)⟫ := hT x y
    _ = ⟪x,compression T U y⟫ := (inner_compression U x y).symm

theorem finrank_prefix {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    finrank ℝ (spectralSpan b (↑(Finset.Iic i) : Set (Fin n))) = i.val + 1 := by
  rw [finrank_spectralSpan, Nat.card_eq_fintype_card]
  exact (Fintype.card_ofFinset (Finset.Iic i) (by simp)).trans (Fin.card_Iic i)

theorem finrank_suffix {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    finrank ℝ (spectralSpan b (↑(Finset.Ici i) : Set (Fin n))) = n - i.val := by
  rw [finrank_spectralSpan, Nat.card_eq_fintype_card]
  exact (Fintype.card_ofFinset (Finset.Ici i) (by simp)).trans (Fin.card_Ici i)

/-- Upper half of descending Cauchy interlacing. Multiplicities are unrestricted. -/
theorem compression_eigenvalue_le (hT : T.IsSymmetric) (U : Submodule ℝ E)
    {n m : ℕ} (hn : finrank ℝ E = n) (hm : finrank ℝ U = m)
    (hmn : m ≤ n) (i : Fin m) :
    (compression_symmetric hT U).eigenvalues hm i ≤
      hT.eigenvalues hn (Fin.castLE hmn i) := by
  classical
  let hS := compression_symmetric hT U
  let j := Fin.castLE hmn i
  let A := spectralSpan (hT.eigenvectorBasis hn) (↑(Finset.Ici j) : Set (Fin n))
  let B := spectralSpan (hS.eigenvectorBasis hm) (↑(Finset.Iic i) : Set (Fin m))
  have hA : finrank ℝ A = n - i.val := finrank_suffix _ j
  have hB : finrank ℝ (B.map U.subtype) = i.val + 1 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact finrank_prefix _ i
  obtain ⟨x,hxA,hxB,hx0⟩ := exists_nonzero_intersection A (B.map U.subtype) (by
    rw [hn,hA,hB]
    have hi := i.isLt
    omega)
  obtain ⟨y,hy,rfl⟩ := hxB
  have hlow := rayleigh_ge_of_support hS hm (↑(Finset.Iic i)) (hS.eigenvalues hm i)
    (fun k hk => hS.eigenvalues_antitone hm (by simpa using hk)) hy
  have hupp := rayleigh_le_of_support hT hn (↑(Finset.Ici j)) (hT.eigenvalues hn j)
    (fun k hk => hT.eigenvalues_antitone hn (by simpa using hk)) hxA
  rw [inner_compression] at hlow
  have hp : 0 < ‖(y : E)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hnorm : ‖y‖ = ‖(y : E)‖ := rfl
  rw [hnorm] at hlow
  exact (mul_le_mul_iff_left₀ hp).mp (hlow.trans hupp)

/-- Lower half of descending Cauchy interlacing; the offset is the real codimension. -/
theorem le_compression_eigenvalue (hT : T.IsSymmetric) (U : Submodule ℝ E)
    {n m : ℕ} (hn : finrank ℝ E = n) (hm : finrank ℝ U = m)
    (hmn : m ≤ n) (i : Fin m) :
    hT.eigenvalues hn ⟨i.val + (n-m), by omega⟩ ≤
      (compression_symmetric hT U).eigenvalues hm i := by
  classical
  let hS := compression_symmetric hT U
  let j : Fin n := ⟨i.val+(n-m),by omega⟩
  let A := spectralSpan (hT.eigenvectorBasis hn) (↑(Finset.Iic j) : Set (Fin n))
  let B := spectralSpan (hS.eigenvectorBasis hm) (↑(Finset.Ici i) : Set (Fin m))
  have hA : finrank ℝ A = i.val+(n-m)+1 := finrank_prefix _ j
  have hB : finrank ℝ (B.map U.subtype) = m-i.val := by
    rw [Submodule.finrank_map_subtype_eq]
    exact finrank_suffix _ i
  obtain ⟨x,hxA,hxB,hx0⟩ := exists_nonzero_intersection A (B.map U.subtype) (by
    rw [hn,hA,hB]
    have hi := i.isLt
    omega)
  obtain ⟨y,hy,rfl⟩ := hxB
  have hlow := rayleigh_ge_of_support hT hn (↑(Finset.Iic j)) (hT.eigenvalues hn j)
    (fun k hk => hT.eigenvalues_antitone hn (by simpa using hk)) hxA
  have hupp := rayleigh_le_of_support hS hm (↑(Finset.Ici i)) (hS.eigenvalues hm i)
    (fun k hk => hS.eigenvalues_antitone hm (by simpa using hk)) hy
  rw [inner_compression] at hupp
  have hp : 0 < ‖(y : E)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hnorm : ‖y‖ = ‖(y : E)‖ := rfl
  rw [hnorm] at hupp
  exact (mul_le_mul_iff_left₀ hp).mp (hlow.trans hupp)
end Gaussian.Spectral
