import Gaussian.Physical.Fermion.StateAction

noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

theorem prefixEmbed_word (k l : ℕ) (w : List (MajoranaIndex k)) :
    prefixEmbed k l (wordOperator k w) =
      wordOperator (l+k) (w.map (fun a => (prefixIndex k l a.1,a.2))) := by
  induction w with
  | nil => simp [wordOperator]
  | cons a w ih =>
    rw [wordOperator_cons, prefixEmbed_mul, prefixEmbed_majorana, ih]
    rfl

theorem prefixRestriction_moment (k l : ℕ) (ρ : Density (l+k)) (w : List (MajoranaIndex k)) :
    moment (prefixRestriction k l ρ) w =
      moment ρ (w.map (fun a => (prefixIndex k l a.1,a.2))) := by
  unfold moment
  rw [prefixRestriction_expectation, prefixEmbed_word]

theorem unitary_word_fixed {n : ℕ} (U : Matrix.unitaryGroup (Occupation n) ℂ)
    (w : List (MajoranaIndex n))
    (h : ∀ a ∈ w, (U : Operator n) * majorana n a * (U : Operator n)ᴴ = majorana n a) :
    (U : Operator n) * wordOperator n w * (U : Operator n)ᴴ = wordOperator n w := by
  induction w with
  | nil =>
    change (U : Operator n) * 1 * (U : Operator n)ᴴ = 1
    rw [Matrix.mul_one]
    exact U.property.2
  | cons a w ih =>
    rw [wordOperator_cons, unitary_conjugate_mul, h a (by simp), ih]
    intro b hb
    exact h b (by simp [hb])

theorem implemented_fixed_prefix_marginal (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U)
    (hfix : ∀ a : MajoranaIndex k,
      R (coefficientBasis (l+k) (prefixIndex k l a.1,a.2)) =
        coefficientBasis (l+k) (prefixIndex k l a.1,a.2)) :
    prefixRestriction k l (ρ.uConj U) = prefixRestriction k l ρ := by
  apply density_eq_of_moments
  intro w
  rw [prefixRestriction_moment, prefixRestriction_moment]
  unfold moment
  rw [unitaryState_expectation]
  have hi := implements_inv (l+k) hU
  have hword := unitary_word_fixed U⁻¹
    (w.map (fun a => (prefixIndex k l a.1,a.2))) (by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      have hv : R⁻¹ (coefficientBasis (l+k) (prefixIndex k l b.1,b.2)) =
          coefficientBasis (l+k) (prefixIndex k l b.1,b.2) := by
        apply R.injective
        exact (R.apply_symm_apply _).trans (hfix b).symm
      simpa only [linearMajorana_basis, hv] using
        hi (coefficientBasis (l+k) (prefixIndex k l b.1,b.2)))
  change (U : Operator (l+k))ᴴ * _ * ((U : Operator (l+k))ᴴ)ᴴ = _ at hword
  rw [Matrix.conjTranspose_conjTranspose] at hword
  rw [hword]

end Gaussian.Physical.Fermion
