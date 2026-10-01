import Gaussian.Physical.Boson.PureGaussianRealization
import Gaussian.Phase.BosonicPurificationStandard

/-! Exact equivalence between actual Gaussian rank-one purity and the original raw
compatible covariance condition. Neither direction assumes a normal form or entropy formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma standardPureCovariance_phaseBasis {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (i j : Fin n × Bool) :
    (standardPureCovariance E).form (phaseBasis a.toBasis i) (phaseBasis a.toBasis j)=
      if i=j then 1 else 0 := by
  rcases i with ⟨i,c⟩
  rcases j with ⟨j,d⟩
  cases c <;> cases d <;> by_cases hij : i=j <;>
    simp [standardPureCovariance_form,orthonormal_iff_ite.mp a.orthonormal,hij]

/-- Unit simultaneous Williamson coefficients reconstruct an actual compatible
positive form and its square-minus-identity generator on the original carrier. -/
theorem exists_pureCompatible_of_unit_mode_basis {n : ℕ}
    (a : OrthonormalBasis (Fin n) ℝ E) (b : Basis (Fin n × Bool) ℝ (E×E))
    (V : LinearMap.BilinForm ℝ (E×E))
    (hbV : ∀ i j, V (b i) (b j)=if i=j then 1 else 0)
    (hbΩ : ∀ i j, weylSymplecticForm E (b i) (b j)=
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
        else (if j.2 then 1 else 0)) else 0) :
    ∃ d : PureCompatibleCovariance (weylSymplecticForm E), d.form=V := by
  let R := normalFormEquiv a b
  have hR : (weylSymplecticForm E).compl₁₂ R.toLinearMap R.toLinearMap=weylSymplecticForm E := by
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    exact normalFormEquiv_symplectic a b hbΩ z w
  let d0 : PureCompatibleCovariance (weylSymplecticForm E) := standardPureCovariance E
  let d := (d0.pullback R).of_form_eq hR
  refine ⟨d,?_⟩
  apply b.ext
  intro i
  apply b.ext
  intro j
  change ((d0.pullback R).of_form_eq hR).form (b i) (b j)=V (b i) (b j)
  rw [PureCompatibleCovariance.of_form_eq_form,PureCompatibleCovariance.pullback_form]
  change (standardPureCovariance E).form (normalFormEquiv a b (b i))
    (normalFormEquiv a b (b j))=_
  rw [normalFormEquiv_basis,normalFormEquiv_basis,standardPureCovariance_phaseBasis,hbV]

/-- Every actual pure normal Gaussian belongs to the raw covariance-purity domain,
including arbitrary first moments, pure degeneracies and empty mode spaces. -/
theorem IsGaussianWith.exists_pureCompatible_of_isPure {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) (hp : ρ.IsPure) :
    ∃ d : PureCompatibleCovariance (weylSymplecticForm E), d.form=V := by
  classical
  obtain ⟨ν,b,hν,hbV,hbΩ⟩ := exists_williamson_phase_basis V hρ.1 hρ.uncertainty
  have he := hρ.entropy_eq_bosonFormCost b
  rw [bosonFormCost_eq_sum_of_mode_basis b b V (weylSymplecticForm E)
    hρ.1 weylSymplecticForm_isAlt ν hν hbV hbΩ,hp.entropy_eq_zero] at he
  have hsum : ∑ i, Gaussian.Entropy.boson (ν i)=0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp he.symm)
      (Finset.sum_nonneg (fun i hi => Gaussian.Entropy.boson_nonneg (hν i)))
  have hνone : ∀ i, ν i=1 := by
    intro i
    apply (Gaussian.Entropy.boson_eq_zero_iff (hν i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => Gaussian.Entropy.boson_nonneg (hν j))).mp hsum i (Finset.mem_univ i)
  apply exists_pureCompatible_of_unit_mode_basis (stdOrthonormalBasis ℝ E) b V _ hbΩ
  intro i j
  rw [hbV,hνone]

theorem IsGaussianWith.isPure_iff_exists_pureCompatible {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.IsPure ↔ ∃ d : PureCompatibleCovariance (weylSymplecticForm E), d.form=V := by
  refine ⟨hρ.exists_pureCompatible_of_isPure,?_⟩
  rintro ⟨d,hd⟩
  exact IsGaussianWith.isPure_of_compatible d (hd.symm ▸ hρ)

end Gaussian.Physical.Boson
