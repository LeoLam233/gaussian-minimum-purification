import Gaussian.Physical.Fermion.CompressionBridge
import Gaussian.Physical.Fermion.PurityBridge

set_option autoImplicit false
noncomputable section
open Module Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

/-- Exact equality of actual state entropies forces an exact pure endpoint on
the discarded adapted coefficient space, including a zero cross block. -/
theorem quasifree_compression_entropy_rigidity {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (V : Submodule ℝ (CoefficientSpace n)) (hV : d.complexStructure.IsInvariant V)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] V)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) V (e x))
    (he : Sᵥₙ σ=Sᵥₙ ρ) :
    (∀ x ∈ Vᗮ,d.K x=x) ∧ (∀ x ∈ Vᗮ,∀ y ∈ V,⟪d.K y,x⟫=0) := by
  have hk : finrank ℝ V=2*k := by
    rw [← e.toLinearEquiv.finrank_eq]
    simp [CoefficientSpace,MajoranaIndex,Nat.mul_comm]
  have hn : finrank ℝ (CoefficientSpace n)=finrank ℝ Vᗮ+2*k := by
    have h := V.finrank_add_finrank_orthogonal
    omega
  rw [quasifree_entropy_of_isometry_adaptation σ hσ (d.compressed V hV) e hT hk,
    quasifree_entropy_of_adaptation_dim ρ hρ d hn] at he
  exact Gaussian.Entropy.fermion_compression_rigidity d.positive
    (d.one_sub_positive (covarianceGenerator_contraction ρ)) V hn hk he

/-- A real endpoint compression is a genuine pure actual Wick density when its
trace-defined generator is proved to be that compression. -/
theorem quasifree_pure_of_adapted_endpoint {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (V : Submodule ℝ (CoefficientSpace n)) (hV : d.complexStructure.IsInvariant V)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] V)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) V (e x))
    (hK : ∀ x ∈ V,d.K x=x) : ∃ ψ,σ=MState.pure ψ := by
  let q := d.compressed V hV
  have hc (x : V) : compression d.K V x=x := by
    apply ext_inner_left ℝ
    intro y
    rw [inner_compression,hK x x.property]
    rfl
  have ht (x : V) : compression (covarianceGenerator ρ) V x=q.J x := by
    rw [q.factor]
    change q.J (compression d.K V x)=q.J x
    rw [hc]
  apply (quasifree_pure_iff_covariancePure k σ hσ).mpr
  intro x
  apply e.injective
  rw [hT,hT,ht,ht,q.square_neg,map_neg]

end Gaussian.Physical.Fermion
