import Gaussian.Physical.Fermion.PhysicalSubspace

/-! Closedness of the raw finite CAR Wick state domain and continuity of genuine
matrix partial traces, for actual-state compactness and entropy attainment. -/
noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

@[fun_prop] theorem continuous_moment (n : ℕ) (w : List (MajoranaIndex n)) :
    Continuous (fun ρ : Density n => moment ρ w) := by
  unfold moment
  fun_prop

@[fun_prop] theorem continuous_wickMoment (n : ℕ) (w : List (MajoranaIndex n)) :
    Continuous (fun ρ : Density n => wickValue (fun a b => moment ρ [a,b]) w) := by
  induction w using wickValue.induct with
  | case1 => simpa only [wickValue_nil] using (continuous_const : Continuous (fun _ : Density n => (1:ℂ)))
  | case2 a w ih =>
    simp only [wickValue]
    apply continuous_finsetSum
    intro i hi
    exact (continuous_const.mul (continuous_moment n [a,w.get i])).mul (ih i)

theorem isClosed_quasifree (n : ℕ) : IsClosed {ρ : Density n | IsQuasifree ρ} := by
  have hs : {ρ : Density n | IsQuasifree ρ} =
      ⋂ w : List (MajoranaIndex n), {ρ | moment ρ w = wickValue (fun a b => moment ρ [a,b]) w} := by
    ext ρ
    simp only [Set.mem_setOf_eq,Set.mem_iInter,isQuasifree_iff_wick]
  rw [hs]
  exact isClosed_iInter (fun w => isClosed_eq (continuous_moment n w) (continuous_wickMoment n w))

@[fun_prop] theorem continuous_state_purity (n : ℕ) :
    Continuous (fun ρ : Density n => (ρ.purity : ℝ)) := by
  change Continuous (fun ρ : Density n => ⟪ρ.M,ρ.M⟫)
  fun_prop

theorem isClosed_pure (n : ℕ) : IsClosed {ρ : Density n | ∃ ψ,ρ=MState.pure ψ} := by
  have hs : {ρ : Density n | ∃ ψ,ρ=MState.pure ψ} = {ρ | (ρ.purity:ℝ)=1} := by
    ext ρ
    simp only [Set.mem_setOf_eq,MState.pure_iff_purity_one]
    exact Subtype.ext_iff
  rw [hs]
  exact isClosed_eq (continuous_state_purity n) continuous_const

theorem isClosed_pureQuasifree (n : ℕ) : IsClosed {ρ : Density n | IsPureQuasifree ρ} :=
  (isClosed_quasifree n).inter (isClosed_pure n)

set_option backward.isDefEq.respectTransparency false in
@[fun_prop] theorem continuous_prefixRestriction (k l : ℕ) :
    Continuous (prefixRestriction k l) := by
  rw [continuous_induced_rng,continuous_induced_rng]
  change Continuous (fun ρ : Density (l+k) =>
    ((ρ.m).submatrix (occupationSplit k l).symm (occupationSplit k l).symm).traceRight)
  unfold Matrix.traceRight
  fun_prop

@[fun_prop] theorem continuous_prefixEntropy (k l : ℕ) :
    Continuous (fun ρ : Density (l+k) => Sᵥₙ (prefixRestriction k l ρ)) :=
  Sᵥₙ_continuous.comp (continuous_prefixRestriction k l)

/-- The genuine pure Gaussian purifiers of a fixed actual density form a compact set. -/
theorem isCompact_quasifreePurifiers (k l : ℕ) (ρ : Density k) :
    IsCompact {σ : Density (l+k) | IsPureQuasifree σ ∧ prefixRestriction k l σ=ρ} := by
  exact ((isClosed_pureQuasifree (l+k)).inter
    (isClosed_eq (continuous_prefixRestriction k l) continuous_const)).isCompact

/-- Any continuous physical objective attains a minimum over a nonempty
fixed-size actual pure Gaussian purification class. -/
theorem exists_minimum_quasifreePurifiers (k l : ℕ) (ρ : Density k)
    (hnonempty : ∃ σ : Density (l+k),IsPureQuasifree σ ∧ prefixRestriction k l σ=ρ)
    (f : Density (l+k) → ℝ) (hf : Continuous f) :
    ∃ σ : Density (l+k),IsPureQuasifree σ ∧ prefixRestriction k l σ=ρ ∧
      ∀ τ : Density (l+k),IsPureQuasifree τ → prefixRestriction k l τ=ρ → f σ≤f τ := by
  obtain ⟨σ,hσ,hmin⟩ := (isCompact_quasifreePurifiers k l ρ).exists_isMinOn hnonempty hf.continuousOn
  exact ⟨σ,hσ.1,hσ.2,fun τ hτ hm => hmin ⟨hτ,hm⟩⟩

/-- Unconditional finite-size minimum existence for any actual raw Wick input,
using the proved n-mode auxiliary Gaussian purifier construction. -/
theorem exists_minimum_doubled_quasifreePurifiers (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ)
    (f : Density (n+n) → ℝ) (hf : Continuous f) :
    ∃ σ : Density (n+n),IsPureQuasifree σ ∧ prefixRestriction n n σ=ρ ∧
      ∀ τ : Density (n+n),IsPureQuasifree τ → prefixRestriction n n τ=ρ → f σ≤f τ :=
  exists_minimum_quasifreePurifiers n n ρ (exists_quasifree_purification n ρ hρ) f hf

end Gaussian.Physical.Fermion
