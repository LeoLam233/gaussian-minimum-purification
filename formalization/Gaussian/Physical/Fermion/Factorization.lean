import Gaussian.Physical.Fermion.Thermal

noncomputable section
open scoped MState
namespace Gaussian.Physical.Fermion

theorem pure_density_factors_of_pure_right {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : MState (d × e)) (hp : ∃ ψ, ρ = MState.pure ψ)
    (hr : ∃ φ, ρ.traceLeft = MState.pure φ) :
    ρ = ρ.traceRight.prod ρ.traceLeft := by
  obtain ⟨ψ,rfl⟩ := hp
  have hs := (MState.pure_separable_iff_traceLeft_pure ψ).mpr
    (by obtain ⟨φ,hφ⟩ := hr; exact ⟨φ,hφ.symm⟩)
  obtain ⟨ξ,φ,hψ⟩ := MState.pure_separable_imp_IsProd ψ hs
  rw [hψ, MState.pure_prod_pure, MState.traceRight_prod_eq, MState.traceLeft_prod_eq]

theorem pure_density_factors_of_pure_left {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : MState (d × e)) (hp : ∃ ψ, ρ = MState.pure ψ)
    (hl : ∃ φ, ρ.traceRight = MState.pure φ) :
    ρ = ρ.traceRight.prod ρ.traceLeft := by
  have hps : ∃ ψ, ρ.SWAP = MState.pure ψ := by
    obtain ⟨ψ,rfl⟩ := hp
    exact MState.relabel_pure_exists ψ _
  have hs := pure_density_factors_of_pure_right ρ.SWAP hps (by simpa using hl)
  have he := congrArg MState.SWAP hs
  rw [MState.SWAP_SWAP, MState.traceRight_SWAP, MState.traceLeft_SWAP] at he
  calc
    ρ = (ρ.traceLeft.prod ρ.traceRight).SWAP := he
    _ = ρ.traceRight.prod ρ.traceLeft := by
      apply MState.ext_m
      ext ⟨i,j⟩ ⟨k,l⟩
      change ρ.traceLeft.m j l * ρ.traceRight.m i k = ρ.traceRight.m i k * ρ.traceLeft.m j l
      exact mul_comm _ _

theorem entropy_delete_pure_right {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : MState d) (ψ : Ket e) : Sᵥₙ (ρ.prod (MState.pure ψ)) = Sᵥₙ ρ := by
  rw [entropy_prod, Sᵥₙ_of_pure_zero, add_zero]

end Gaussian.Physical.Fermion
