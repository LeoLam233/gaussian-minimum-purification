import Gaussian.Entropy.Scalar
import Gaussian.Spectral.Interlacing

/-! Finite real-list entropy comparison and exact endpoint rigidity.
The physical spectrum correspondence is a separate obligation. -/
noncomputable section
namespace Gaussian.Entropy

/-- Half of the real spectral sum. Physical mode pairing must justify using this cost. -/
def realListCost {n : ℕ} (s : ℝ → ℝ) (a : Fin n → ℝ) : ℝ := (∑ i, s (a i))/2

private theorem sum_rigidity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → ℝ) (d : κ → ℝ) (hab : ∀ i, b i ≤ a i) (hd : ∀ j, 0 ≤ d j)
    (he : ∑ i, a i + ∑ j, d j = ∑ i, b i) :
    (∀ i, a i = b i) ∧ (∀ j, d j = 0) := by
  have hs : (∑ i, b i) ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hab i)
  have hd' : 0 ≤ ∑ j, d j := Finset.sum_nonneg (fun j _ => hd j)
  have hd0 : ∑ j, d j = 0 := by linarith
  have hab0 : ∑ i, b i = ∑ i, a i := by linarith
  constructor
  · intro i
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hab j)).mp hab0 i (Finset.mem_univ i)).symm
  · intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).mp hd0 j (Finset.mem_univ j)

/-- The upper-interlacing comparison used for bosons, with all omitted terms included. -/
theorem boson_prefix_comparison {m c : ℕ} (a : Fin (m+c) → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 1 ≤ a i) (hb : ∀ i, 1 ≤ b i)
    (hab : ∀ i, b i ≤ a (Fin.castAdd c i)) :
    realListCost boson b ≤ realListCost boson a := by
  unfold realListCost
  rw [Fin.sum_univ_add]
  have hk : (∑ i, boson (b i)) ≤ ∑ i, boson (a (Fin.castAdd c i)) :=
    Finset.sum_le_sum (fun i _ => strictMonoOn_boson.monotoneOn (hb i) (ha _) (hab i))
  have hd : 0 ≤ ∑ j : Fin c, boson (a (Fin.natAdd m j)) :=
    Finset.sum_nonneg (fun j _ => boson_nonneg (ha _))
  linarith

theorem boson_prefix_rigidity {m c : ℕ} (a : Fin (m+c) → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 1 ≤ a i) (hb : ∀ i, 1 ≤ b i)
    (hab : ∀ i, b i ≤ a (Fin.castAdd c i))
    (he : realListCost boson b = realListCost boson a) :
    (∀ i, a (Fin.castAdd c i) = b i) ∧ (∀ j, a (Fin.natAdd m j) = 1) := by
  have hs : (∑ i, boson (a (Fin.castAdd c i))) +
      (∑ j, boson (a (Fin.natAdd m j))) = ∑ i, boson (b i) := by
    unfold realListCost at he
    rw [Fin.sum_univ_add] at he
    linarith
  have h := sum_rigidity (fun i => boson (a (Fin.castAdd c i))) (fun i => boson (b i))
    (fun j => boson (a (Fin.natAdd m j)))
    (fun i => strictMonoOn_boson.monotoneOn (hb i) (ha _) (hab i))
    (fun _ => boson_nonneg (ha _)) hs
  exact ⟨fun i => strictMonoOn_boson.injOn (ha _) (hb i) (h.1 i),
    fun j => (boson_eq_zero_iff (ha _)).mp (h.2 j)⟩

/-- Fermions use the lower-interlacing bound; the omitted terms are the initial prefix. -/
theorem fermion_suffix_comparison {c m : ℕ} (a : Fin (c+m) → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Set.Icc (0:ℝ) 1)
    (hab : ∀ i, a (Fin.natAdd c i) ≤ b i) :
    realListCost fermion b ≤ realListCost fermion a := by
  unfold realListCost
  rw [Fin.sum_univ_add]
  have hk : (∑ i, fermion (b i)) ≤ ∑ i, fermion (a (Fin.natAdd c i)) :=
    Finset.sum_le_sum (fun i _ => strictAntiOn_fermion.antitoneOn (ha _) (hb i) (hab i))
  have hd : 0 ≤ ∑ j : Fin c, fermion (a (Fin.castAdd m j)) :=
    Finset.sum_nonneg (fun j _ => fermion_nonneg (ha _))
  linarith

theorem fermion_suffix_rigidity {c m : ℕ} (a : Fin (c+m) → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Set.Icc (0:ℝ) 1)
    (hab : ∀ i, a (Fin.natAdd c i) ≤ b i)
    (he : realListCost fermion b = realListCost fermion a) :
    (∀ i, a (Fin.natAdd c i) = b i) ∧ (∀ j, a (Fin.castAdd m j) = 1) := by
  have hs : (∑ i, fermion (a (Fin.natAdd c i))) +
      (∑ j, fermion (a (Fin.castAdd m j))) = ∑ i, fermion (b i) := by
    unfold realListCost at he
    rw [Fin.sum_univ_add] at he
    linarith
  have h := sum_rigidity (fun i => fermion (a (Fin.natAdd c i))) (fun i => fermion (b i))
    (fun j => fermion (a (Fin.castAdd m j)))
    (fun i => strictAntiOn_fermion.antitoneOn (ha _) (hb i) (hab i))
    (fun _ => fermion_nonneg (ha _)) hs
  exact ⟨fun i => strictAntiOn_fermion.injOn (ha _) (hb i) (h.1 i),
    fun j => (fermion_eq_zero_iff (ha _)).mp (h.2 j)⟩
end Gaussian.Entropy
