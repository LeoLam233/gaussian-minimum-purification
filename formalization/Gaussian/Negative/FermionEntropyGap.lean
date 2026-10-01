import Gaussian.Entropy.Scalar
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! N2: the entropy gap at a fermionic zero normal parameter has vanishing
first derivative. No universal linear impurity-from-gap estimate is possible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Gaussian.Negative
open Filter
open scoped Topology

theorem fermion_zero_eq_log_two : Gaussian.Entropy.fermion 0=Real.log 2 := by
  norm_num [Gaussian.Entropy.fermion,Real.negMulLog,Real.log_div]
  ring

def fermionZeroGap (δ : ℝ) : ℝ := Gaussian.Entropy.fermion 0-Gaussian.Entropy.fermion δ

theorem fermionZeroGap_eq (δ : ℝ) :
    fermionZeroGap δ=Real.log 2-Gaussian.Entropy.fermion δ := by
  rw [fermionZeroGap,fermion_zero_eq_log_two]

theorem fermionZeroGap_hasDerivAt_zero : HasDerivAt fermionZeroGap 0 0 := by
  have h : HasDerivAt Gaussian.Entropy.fermion (0:ℝ) (0:ℝ) := by
    simpa using Gaussian.Entropy.hasDerivAt_fermion (x := 0) (by constructor <;> norm_num)
  change HasDerivAt (fun x : ℝ => Gaussian.Entropy.fermion 0-Gaussian.Entropy.fermion x) 0 0
  simpa only [neg_zero] using h.const_sub (Gaussian.Entropy.fermion 0)

theorem fermionZeroGap_div_tendsto_zero :
    Tendsto (fun δ : ℝ => fermionZeroGap δ/δ) (𝓝[>] 0) (𝓝 0) := by
  simpa [fermionZeroGap,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    fermionZeroGap_hasDerivAt_zero.tendsto_slope_zero_right

/-- A fixed multiple of the entropy gap cannot control the positive parameter,
even arbitrarily close to zero. This is the precise N2 linear-bound trap. -/
theorem no_linear_impurity_bound (C ε : ℝ) (hC : 0<C) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ δ<min 1 ε ∧ 0<Real.log 2-Gaussian.Entropy.fermion δ ∧
      C*(Real.log 2-Gaussian.Entropy.fermion δ)<δ := by
  have hgap : ∀ᶠ δ : ℝ in 𝓝[>] 0,fermionZeroGap δ/δ<1/C :=
    fermionZeroGap_div_tendsto_zero.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/C))
  have hs0 : ∀ᶠ δ : ℝ in 𝓝 (0:ℝ),δ<min 1 ε :=
    Iio_mem_nhds (lt_min zero_lt_one hε)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0,δ<min 1 ε :=
    hs0.filter_mono nhdsWithin_le_nhds
  have hposEv : ∀ᶠ δ : ℝ in 𝓝[>] 0,0<δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hsmall,hgap⟩ := (hposEv.and (hsmall.and hgap)).exists
  have hδpos : 0<δ := hδ
  have hδone : δ<1 := hsmall.trans_le (min_le_left _ _)
  have hpos : 0<fermionZeroGap δ := sub_pos.mpr
    (Gaussian.Entropy.strictAntiOn_fermion (by simp) ⟨hδpos.le,hδone.le⟩ hδpos)
  refine ⟨δ,hδpos,hsmall,?_,?_⟩
  · simpa only [fermionZeroGap_eq] using hpos
  · have hh := (div_lt_iff₀ hδpos).mp hgap
    have hm := mul_lt_mul_of_pos_left hh hC
    have he : C*((1/C)*δ)=δ := by field_simp
    rw [he] at hm
    simpa only [fermionZeroGap_eq] using hm

end Gaussian.Negative
