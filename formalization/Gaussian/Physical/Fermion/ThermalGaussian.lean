import Gaussian.Physical.Fermion.ThermalCAR
import Gaussian.Physical.Fermion.ParityWick
import Gaussian.Physical.Fermion.WordTransport

/-! Actual thermal and orthogonally rotated thermal densities satisfy the raw
parity-invariant Wick definition.  This is proved from endpoint-safe Ward
identities, not asserted as an interface field or a spectral definition. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion

/-- Full Wick rule for arbitrary real linear CAR fields of the actual thermal density. -/
theorem thermal_linear_Wick (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) (l : List (CoefficientSpace n)) :
    matrixWordMoment (thermal n t ht).m (linearMajorana n) l =
      wickValue (fun a b => matrixWordMoment (thermal n t ht).m (linearMajorana n) [a,b]) l := by
  apply matrixWordMoment_wick (thermal n t ht).m (parity n) (linearMajorana n)
    (thermal n t ht).tr' (parity_square n) (thermal_parityInvariant n t ht)
    (parity_conjugate_linearMajorana n) ?_ l
  exact thermal_linearMajorana_mem_Ward n t ht

/-- Canonical product density is genuinely quasifree at every allowed signed
parameter, including empty, zero, repeated and pure endpoint cases. -/
theorem thermal_isQuasifree (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1) : IsQuasifree (thermal n t ht) := by
  apply isQuasifree_of_wick
  intro w
  have h := matrixWordMoment_wick_map (thermal n t ht).m (linearMajorana n)
    (coefficientBasis n) (thermal_linear_Wick n t ht) w
  simpa only [linearMajorana_basis,matrixWordMoment,moment,wordOperator] using h

/-- Every actually implemented orthogonal image of the canonical thermal density
satisfies the same raw quasifree predicate, in both orthogonal components. -/
theorem rotated_thermal_isQuasifree (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (U : Matrix.unitaryGroup (Occupation n) ℂ) (hU : Implements n R U) :
    IsQuasifree ((thermal n t ht).uConj U) := by
  let f : MajoranaIndex n → Operator n := fun a => linearMajorana n (R⁻¹ (coefficientBasis n a))
  have hleft : (U : Operator n)ᴴ*(U : Operator n)=1 := U.property.1
  have hright : (U : Operator n)*(U : Operator n)ᴴ=1 := U.property.2
  have hc : ∀ a, (U : Operator n)ᴴ*majorana n a*(U : Operator n)=f a := by
    intro a
    have h := implements_inv n hU (coefficientBasis n a)
    change (U : Operator n)ᴴ*linearMajorana n (coefficientBasis n a)*
      ((U : Operator n)ᴴ)ᴴ = _ at h
    simpa only [linearMajorana_basis,Matrix.conjTranspose_conjTranspose] using h
  have hf : ∀ l, matrixWordMoment (thermal n t ht).m f l =
      wickValue (fun a b => matrixWordMoment (thermal n t ht).m f [a,b]) l :=
    matrixWordMoment_wick_map (thermal n t ht).m (linearMajorana n)
      (fun a => R⁻¹ (coefficientBasis n a)) (thermal_linear_Wick n t ht)
  apply isQuasifree_of_wick
  intro w
  have h := matrixWordMoment_transform_wick (thermal n t ht).m
    (U : Operator n) (U : Operator n)ᴴ hright hleft (majorana n) f hc hf w
  exact h

end Gaussian.Physical.Fermion
