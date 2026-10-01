import Gaussian.Physical.Fermion.ParityEndpoints
import Gaussian.Physical.Fermion.Quasifree

/-! Pure parity-invariant actual density states have exactly one of the two
definite total parity signs.  This closes the parity-domain interpretation
without imposing a preferred parity on the optimization. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

theorem occupationParity_eq_sign (n : ℕ) (x : Occupation n) :
    occupationParity n x=1 ∨ occupationParity n x = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih x.2 with h | h <;> cases hx : x.1 <;> simp [occupationParity,h,hx]

theorem occupationParity_mul_self (n : ℕ) (x : Occupation n) :
    occupationParity n x*occupationParity n x=1 := by
  rcases occupationParity_eq_sign n x with h | h <;> simp [h]

/-- A pure actual density commuting with the diagonal parity involution is
supported in a single parity eigenspace, including either sign. -/
theorem pure_parityInvariant_definite {n : ℕ} (ρ : Density n)
    (hpure : ∃ ψ,ρ=MState.pure ψ) (hP : ParityInvariant ρ) :
    ∃ odd : Bool,HasParity ρ odd := by
  obtain ⟨ψ,rfl⟩ := hpure
  obtain ⟨k,hk⟩ := ψ.exists_ne_zero
  have hs (i : Occupation n) (hi : ψ i≠0) : occupationParity n i=occupationParity n k := by
    have h := congrFun₂ hP i k
    change (parity n*(MState.pure ψ).m*parity n) i k = (MState.pure ψ).m i k at h
    rw [parity_diagonal] at h
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,MState.pure_apply] at h
    have hn : ψ i * star (ψ k)≠0 := mul_ne_zero hi (star_ne_zero.mpr hk)
    have hsign : occupationParity n i*occupationParity n k=1 := by
      apply mul_right_cancel₀ hn
      calc
        (occupationParity n i*occupationParity n k)*(ψ i*star (ψ k)) =
          occupationParity n i*(ψ i*star (ψ k))*occupationParity n k := by ring
        _ = 1*(ψ i*star (ψ k)) := by simpa using h
    calc
      occupationParity n i = occupationParity n i*(occupationParity n k*occupationParity n k) := by
        rw [occupationParity_mul_self,mul_one]
      _ = (occupationParity n i*occupationParity n k)*occupationParity n k := by ring
      _ = occupationParity n k := by rw [hsign,one_mul]
  have he : parity n*(MState.pure ψ).m = occupationParity n k • (MState.pure ψ).m := by
    rw [parity_diagonal]
    ext i j
    simp only [Matrix.diagonal_mul,Matrix.smul_apply,MState.pure_apply,smul_eq_mul]
    by_cases hi : ψ i=0
    · simp [hi]
    · rw [hs i hi]
  rcases occupationParity_eq_sign n k with hk | hk
  · exact ⟨false,by simpa only [HasParity,Bool.false_eq_true,if_false,hk] using he⟩
  · exact ⟨true,by simpa only [HasParity,if_true,hk] using he⟩

theorem pure_parityInvariant_iff_definite {n : ℕ} (ρ : Density n)
    (hpure : ∃ ψ,ρ=MState.pure ψ) :
    ParityInvariant ρ ↔ ∃ odd : Bool,HasParity ρ odd := by
  constructor
  · exact pure_parityInvariant_definite ρ hpure
  · rintro ⟨odd,h⟩
    exact hasParity_parityInvariant ρ odd h

/-- The raw pure Wick optimization domain is the union of the two actual
definite total parity components, rather than merely admitting examples of each. -/
theorem pure_quasifree_has_definiteParity {n : ℕ} (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    ∃ odd : Bool,HasParity ρ odd :=
  pure_parityInvariant_definite ρ hρ.2 hρ.1.1

/-- A normalized actual state cannot have both total parity signs. -/
theorem not_both_definiteParity {n : ℕ} (ρ : Density n) :
    ¬(HasParity ρ false ∧ HasParity ρ true) := by
  rintro ⟨he,ho⟩
  change parity n*ρ.m=(1:ℂ) • ρ.m at he
  change parity n*ρ.m=(-1:ℂ) • ρ.m at ho
  have h := congrArg Matrix.trace (he.symm.trans ho)
  norm_num [Matrix.trace_smul,ρ.tr'] at h

theorem pure_quasifree_uniqueParity {n : ℕ} (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    ∃! odd : Bool,HasParity ρ odd := by
  obtain ⟨odd,hodd⟩ := pure_quasifree_has_definiteParity ρ hρ
  refine ⟨odd,hodd,?_⟩
  intro other hother
  cases odd <;> cases other
  · rfl
  · exact (not_both_definiteParity ρ ⟨hodd,hother⟩).elim
  · exact (not_both_definiteParity ρ ⟨hother,hodd⟩).elim
  · rfl

end Gaussian.Physical.Fermion
