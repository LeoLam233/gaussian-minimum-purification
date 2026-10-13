# Verbatim declaration register

Companion to the [formalization verification appendix](README.md), version 1.0, 13 October 2026.

The excerpts below are copied from the frozen v0.1.3 sources. Each entry includes the file-scoped `variable` blocks and namespace/open context preceding the declaration, followed by the exact theorem type or definition. Context is a reading aid, not a standalone Lean file. The source link also exposes the proof and imports; imported definitions and instances remain part of the type. Some context variables do not occur in a particular declaration and are not its hypotheses. No proof body is reproduced for theorems. The register is intentionally selective, not an index of every lemma in all 308 source files.

The machine-readable [registry](declarations.json) pins names, complete-file hashes and line ranges. Run `python scripts/verify_formalization_appendix.py` from the repository root to check the excerpts. That command checks documentation identity; the separate Lean workflow checks compilation and root axioms.

## B01

`Gaussian.Physical.Boson.exists_matched_global_gaussian_purification`

**Paper node:** Theorem 2.1.

**Reading and coverage:** An actual pure Gaussian four-party normal density at counts (nA,nB) has finite entropy, equals the all-finite infimum, and beats every finite sidewise competitor.

**Limits / premises to retain:** Input is an actual BipartiteDensity and IsGaussian. Natural counts include zero. Competitors must satisfy IsSidewisePurifier; no comparison with non-Gaussian purifiers.

[Frozen source, lines 17–23](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GlobalMinimum.lean#L17-L23)

```lean
open Module Gaussian.Phase WithLp
namespace Gaussian.Physical.Boson

theorem exists_matched_global_gaussian_purification (nA nB : ℕ)
    (ρ : BipartiteDensity nA nB) (hρ : IsGaussian ρ) :
    ∃ σ : FourPartyDensity nA nB nA nB,
      IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
      sidewiseEntropy σ=gaussianPurificationInfimum nA nB ρ ∧
      ∀ mA mB : ℕ,∀ τ : FourPartyDensity nA nB mA mB,
        IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ
```

## F01

`Gaussian.Physical.Fermion.exists_matched_global_gaussian_purification`

**Paper node:** Theorem 2.1.

**Reading and coverage:** An actual matched pure Wick density attains the all-finite infimum and beats every independently finite auxiliary pair.

**Limits / premises to retain:** Input is Density (nA+nB) and IsQuasifree. Both definite total parities are permitted. No separately prescribed parity or non-Gaussian comparison.

[Frozen source, lines 14–21](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/GlobalMinimum.lean#L14-L21)

```lean
namespace Gaussian.Physical.Fermion

theorem exists_matched_global_gaussian_purification (nA nB : ℕ)
    (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ=gaussianPurificationInfimum nA nB ρ ∧
      ∀ (mA mB : ℕ) (τ : Density ((mA+mB)+(nA+nB))),
        IsSidewisePurifier nA nB mA mB ρ τ →
          sidewiseEntropy nA nB nA nB σ≤sidewiseEntropy nA nB mA mB τ
```

## D01

`Gaussian.Physical.Boson.IsGaussianWith`

**Paper node:** Section 2, centered states and covariance conventions.

**Reading and coverage:** Raw Weyl characteristic Gaussianity with symmetric real covariance and a finite real linear mean.

**Limits / premises to retain:** Normal-density semantics and finite-dimensional real configuration space are inherited. Uncertainty, purity and entropy identities are proved later, not fields.

[Frozen source, lines 15–18](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianPredicate.lean#L15-L18)

```lean
open MeasureTheory
open scoped InnerProductSpace
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def IsGaussianWith (ρ : NormalDensity (Schrodinger E))
    (m : (E × E) →ₗ[ℝ] ℝ) (V : LinearMap.BilinForm ℝ (E × E)) : Prop :=
  V.IsSymm ∧ ∀ q p, ρ.characteristic q p =
    Complex.exp ((m (q,p) : ℂ)*Complex.I - (V (q,p) (q,p) : ℂ)/4)
```

## D02

`Gaussian.Physical.Boson.IsGaussian`

**Paper node:** Section 2.

**Reading and coverage:** Existential quantification over a mean and symmetric covariance satisfying the raw characteristic predicate.

**Limits / premises to retain:** Does not restrict to zero mean, a canonical spectrum, or a chosen purification ansatz.

[Frozen source, lines 14–15](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianState.lean#L14-L15)

```lean
namespace Gaussian.Physical.Boson
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def IsGaussian (ρ : NormalDensity (Schrodinger E)) : Prop :=
  ∃ m V,IsGaussianWith ρ m V
```

## D03

`Gaussian.Physical.Boson.IsSidewisePurifier`

**Paper node:** Equation (2.1), Gaussian optimization domain.

**Reading and coverage:** Actual pure Gaussian extension with exact AB normal-density partial trace.

**Limits / premises to retain:** Finite-dimensional A,B,C,D configuration spaces; no entropy or optimality is a domain field.

[Frozen source, lines 31–33](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/SidewiseDomain.lean#L31-L33)

```lean
open WithLp
namespace Gaussian.Physical.Boson
variable {A B C D : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

def IsSidewisePurifier (ρ : NormalDensity (Schrodinger (JointConfiguration A B)))
    (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) : Prop :=
  IsPureGaussian σ ∧ σ.leftReduction=ρ
```

## D04

`Gaussian.Physical.Boson.sidewiseEntropy`

**Paper node:** Equation (2.1), objective.

**Reading and coverage:** Extended von Neumann entropy of the actual reordered AA-prime normal-density reduction.

**Limits / premises to retain:** ENNReal admits infinity for general densities. Gaussian finiteness is separately proved.

[Frozen source, lines 28–29](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/SidewiseDomain.lean#L28-L29)

```lean
open WithLp
namespace Gaussian.Physical.Boson
variable {A B C D : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

def sidewiseEntropy (σ : NormalDensity (Schrodinger (FourConfiguration A B C D))) : ENNReal :=
  (sidewiseReduction σ).entropy
```

## D05

`Gaussian.Physical.Fermion.IsQuasifree`

**Paper node:** Section 2, parity-invariant quasifree input.

**Reading and coverage:** Parity invariance and Wick recursion for all words in actual signed Majorana operators.

**Limits / premises to retain:** No prescribed support parity; a parity-invariant mixed state may occupy both sectors. Does not define Gaussianity by an entropy formula.

[Frozen source, lines 11–13](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/Quasifree.lean#L11-L13)

```lean
open scoped BigOperators
namespace Gaussian.Physical.Fermion

def IsQuasifree {n : ℕ} (ρ : Density n) : Prop :=
  ParityInvariant ρ ∧ ∀ l : List (MajoranaIndex n),
    moment ρ l = wickValue (fun a b => moment ρ [a,b]) l
```

## D06

`Gaussian.Physical.Fermion.IsPureQuasifree`

**Paper node:** Section 2, pure Gaussian competitors.

**Reading and coverage:** Raw IsQuasifree together with equality to an actual pure density.

**Limits / premises to retain:** Neither total parity component is selected.

[Frozen source, lines 16–17](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/Quasifree.lean#L16-L17)

```lean
open scoped BigOperators
namespace Gaussian.Physical.Fermion

def IsPureQuasifree {n : ℕ} (ρ : Density n) : Prop :=
  IsQuasifree ρ ∧ ∃ ψ, ρ = MState.pure ψ
```

## D07

`Gaussian.Physical.Fermion.IsSidewisePurifier`

**Paper node:** Equation (2.1), Gaussian optimization domain.

**Reading and coverage:** Pure Wick density and exact physical prefix restriction.

**Limits / premises to retain:** Density type index adds auxiliary counts first, but the mode labeling is physical A,B then auxiliary A-prime,B-prime. Complete CAR mode restriction is essential.

[Frozen source, lines 48–50](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/SidewiseDomain.lean#L48-L50)

```lean
namespace Gaussian.Physical.Fermion

def IsSidewisePurifier (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+mB)+(nA+nB))) : Prop :=
  IsPureQuasifree σ ∧ prefixRestriction (nA+nB) (mA+mB) σ=ρ
```

## D08

`Gaussian.Physical.Fermion.sidewiseEntropy`

**Paper node:** Equation (2.1), objective.

**Reading and coverage:** Sᵥₙ of the signed complete-mode AA-prime restriction.

**Limits / premises to retain:** Finite occupation-space density, with graded reordering implemented before partial trace.

[Frozen source, lines 44–45](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/SidewiseDomain.lean#L44-L45)

```lean
namespace Gaussian.Physical.Fermion

def sidewiseEntropy (nA nB mA mB : ℕ)
    (σ : Density ((mA+mB)+(nA+nB))) : ℝ := Sᵥₙ (sidewiseRestriction nA nB mA mB σ)
```

## D09

`Gaussian.Phase.PureCompatibleCovariance`

**Paper node:** Sections 2 and 4, raw pure covariance.

**Reading and coverage:** A symmetric strictly positive bilinear form with a compatible symplectic generator squaring to minus identity.

**Limits / premises to retain:** This structure is covariance data. Actual normal-density realization and purity require B04; no entropy/minimum is a field.

[Frozen source, lines 18–25](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationCore.lean#L18-L25)

```lean
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

structure PureCompatibleCovariance (Ω : LinearMap.BilinForm ℝ E) where
  form : LinearMap.BilinForm ℝ E
  generator : E →ₗ[ℝ] E
  symmetric : form.IsSymm
  positive : ∀ x, x ≠ 0 → 0 < form x x
  square_neg : ∀ x, generator (generator x) = -x
  compatible : ∀ x y, form x y = Ω x (generator y)
  symplectic : ∀ x y, Ω (generator x) (generator y) = Ω x y
```

## D10

`Gaussian.Phase.BosonicCovariancePurifier`

**Paper node:** Section 4 and Proposition 4.2.

**Reading and coverage:** Any finite auxiliary real symplectic carrier, pure covariance, fixed physical restriction, and nondegenerate auxiliary split.

**Limits / premises to retain:** Real auxiliary dimension is 2*M. The split is not required to match physical sides; cost and minimum are not fields.

[Frozen source, lines 14–26](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomain.lean#L14-L26)

```lean
universe u
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

structure BosonicCovariancePurifier (V Ω : LinearMap.BilinForm ℝ E) (M : ℕ) where
  (Auxiliary : Type u)
  [auxAdd : AddCommGroup Auxiliary]
  [auxModule : Module ℝ Auxiliary]
  [auxFinite : FiniteDimensional ℝ Auxiliary]
  commutator : LinearMap.BilinForm ℝ Auxiliary
  alternating : commutator.IsAlt
  nondegenerate : commutator.Nondegenerate
  mode_count : finrank ℝ Auxiliary = 2*M
  covariance : PureCompatibleCovariance (productForm Ω commutator)
  physical : ∀ x y, covariance.form (x,0) (y,0) = V x y
  split : Submodule ℝ Auxiliary
  split_nondegenerate : (commutator.restrict split).Nondegenerate
```

## D11

`Gaussian.Physical.Fermion.FinitePurifier`

**Paper node:** Section 4, all fixed-total assignments.

**Reading and coverage:** A Fin (M+1) split index and an actual pure Wick density with the fixed physical prefix.

**Limits / premises to retain:** Both parity components, every split, and all actual densities in that domain are included.

[Frozen source, lines 9–11](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotalDomain.lean#L9-L11)

```lean
namespace Gaussian.Physical.Fermion

def FinitePurifier (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ) :=
  {p : Fin (M+1) × Density (M+(nA+nB)) //
    IsPureQuasifree p.2 ∧ prefixRestriction (nA+nB) M p.2=ρ}
```

## D12

`Gaussian.Physical.Boson.allFinitePurificationCosts`

**Paper node:** Equation (2.1).

**Reading and coverage:** Union of feasible ENNReal entropy values over every mA,mB in the natural numbers.

**Limits / premises to retain:** No size cap. The infimum is sInf of this set; B01 supplies a member attaining it.

[Frozen source, lines 17–19](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/AllFiniteDomain.lean#L17-L19)

```lean
namespace Gaussian.Physical.Boson

def allFinitePurificationCosts (nA nB : ℕ) (ρ : BipartiteDensity nA nB) : Set ENNReal :=
  {s | ∃ mA mB : ℕ,∃ σ : FourPartyDensity nA nB mA mB,
    IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ=s}
```

## D13

`Gaussian.Physical.Fermion.allFinitePurificationCosts`

**Paper node:** Equation (2.1).

**Reading and coverage:** Union of feasible real entropy values over every mA,mB in the natural numbers.

**Limits / premises to retain:** No size cap or fixed parity. F01 supplies a least feasible value, resolving any empty-set concern for quasifree input.

[Frozen source, lines 12–14](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean#L12-L14)

```lean
namespace Gaussian.Physical.Fermion

def allFinitePurificationCosts (nA nB : ℕ) (ρ : Density (nA+nB)) : Set ℝ :=
  {c | ∃ (mA mB : ℕ) (σ : Density ((mA+mB)+(nA+nB))),
    IsSidewisePurifier nA nB mA mB ρ σ ∧ sidewiseEntropy nA nB mA mB σ=c}
```

## B02

`Gaussian.Physical.Boson.existsUnique_gaussian_iff`

**Paper node:** Section 2 and Appendix C, state/covariance semantics.

**Reading and coverage:** Symmetry plus realified uncertainty is equivalent to existence of a unique normal Gaussian density for each prescribed mean.

**Limits / premises to retain:** Finite-dimensional real inner-product configuration space with its Borel structure. Uniqueness is for fixed mean and covariance, not uniqueness of the EoP optimizer.

[Frozen source, lines 14–16](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianEntropyObjective.lean#L14-L16)

```lean
open Module Gaussian.Phase
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem existsUnique_gaussian_iff (m : (E×E) →ₗ[ℝ] ℝ) (V : LinearMap.BilinForm ℝ (E×E)) :
    (∃! ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ m V) ↔
      V.IsSymm ∧ Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E)
```

## B03

`Gaussian.Physical.Boson.IsGaussianWith.entropy_objective`

**Paper node:** Section 2, entropy formula.

**Reading and coverage:** Actual CFC entropy is finite and its toReal equals the independently defined two-form bosonic cost.

**Limits / premises to retain:** Retain Gaussianity and the finite basis; do not apply ENNReal.toReal to arbitrary infinite-entropy densities.

[Frozen source, lines 26–31](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianEntropyObjective.lean#L26-L31)

```lean
open Module Gaussian.Phase
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem IsGaussianWith.entropy_objective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.entropy≠⊤ ∧ ρ.entropy.toReal=
      bosonFormCost e V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt
```

## B04

`Gaussian.Physical.Boson.IsGaussianWith.isPure_iff_exists_pureCompatible`

**Paper node:** Sections 2 and 5, pure covariance/state bridge.

**Reading and coverage:** Actual Gaussian density is pure exactly when its covariance admits PureCompatibleCovariance data.

**Limits / premises to retain:** Gaussianity and the actual normal-density model are essential. Mean may be nonzero.

[Frozen source, lines 75–78](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianPurity.lean#L75-L78)

```lean
open Module Gaussian.Phase
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem IsGaussianWith.isPure_iff_exists_pureCompatible {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.IsPure ↔ ∃ d : PureCompatibleCovariance (weylSymplecticForm E), d.form=V
```

## B05

`Gaussian.Physical.Boson.IsSidewisePurifier.exists_covariancePurifier`

**Paper node:** Theorem 2.1, comparison-domain completeness.

**Reading and coverage:** Every actual four-party competitor yields a raw covariance purifier with both exact counts, finite entropy and the same cost.

**Limits / premises to retain:** Requires IsGaussianWith for the given AB state and an actual IsSidewisePurifier. Covers arbitrary finite C,D; no reference-ansatz restriction.

[Frozen source, lines 23–32](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/CovarianceDomainBridge.lean#L23-L32)

```lean
universe u
open Module Gaussian.Phase WithLp
namespace Gaussian.Physical.Boson
variable {A B C D : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem IsSidewisePurifier.exists_covariancePurifier
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V) (hσ : IsSidewisePurifier ρ σ) :
    ∃ p : BosonicCovariancePurifier V (weylSymplecticForm (JointConfiguration A B))
        (finrank ℝ C+finrank ℝ D),
      p.leftModes=finrank ℝ C ∧ p.rightModes=finrank ℝ D ∧
      sidewiseEntropy σ≠⊤ ∧ (sidewiseEntropy σ).toReal=p.cost (physicalPhaseSubspace A B)
```

## B06

`Gaussian.Physical.Boson.covariancePurifier_exists_sidewise_realization`

**Paper node:** Theorem 2.1, actual witness.

**Reading and coverage:** Every raw purifier is realized as an actual sidewise density with the original AB density, exact side counts and cost.

**Limits / premises to retain:** Requires an actual AB Gaussian density with specified mean/covariance and raw feasible p. Equality of covariance alone is supplemented by Gaussian density uniqueness.

[Frozen source, lines 15–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/CovarianceDomainRealization.lean#L15-L24)

```lean
open Module Gaussian.Phase
namespace Gaussian.Physical.Boson
variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]

theorem covariancePurifier_exists_sidewise_realization
    {ρ : NormalDensity (Schrodinger (JointConfiguration A B))}
    {m : (JointConfiguration A B×JointConfiguration A B) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration A B×JointConfiguration A B)}
    (hρ : IsGaussianWith ρ m V) {M : ℕ}
    (p : BosonicCovariancePurifier V (weylSymplecticForm (JointConfiguration A B)) M) :
    ∃ a b : ℕ, a+b=M ∧ a=p.leftModes ∧ b=p.rightModes ∧
      ∃ σ : NormalDensity (Schrodinger (FourConfiguration A B (CanonicalConfiguration a) (CanonicalConfiguration b))),
        IsSidewisePurifier ρ σ ∧ sidewiseEntropy σ≠⊤ ∧
        (sidewiseEntropy σ).toReal=p.cost (physicalPhaseSubspace A B)
```

## B07

`Gaussian.Phase.exists_bosonic_covariance_allFinite_matched_minimum`

**Paper node:** Theorem 2.1, covariance layer.

**Reading and coverage:** Matched raw covariance at total nA+nB beats every purifier on any finite auxiliary symplectic carrier and split.

**Limits / premises to retain:** V symmetric, Omega alternating/nondegenerate, realified uncertainty, A symplectically nondegenerate, dim E=2*(nA+nB), dim A=2*nA. State semantics are B05/B06.

[Frozen source, lines 21–28](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationMinimum.lean#L21-L28)

```lean
universe u
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem exists_bosonic_covariance_allFinite_matched_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (nA nB : ℕ) (hd : finrank ℝ E=2*(nA+nB)) (hAd : finrank ℝ A=2*nA) :
    ∃ p : BosonicCovariancePurifier V Ω (nA+nB),
      p.leftModes=nA ∧ p.rightModes=nB ∧
      ∀ M : ℕ, ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A
```

## B08

`Gaussian.Phase.exists_bosonic_covariance_selection`

**Paper node:** Lemma 3.1, bosonic selection.

**Reading and coverage:** Constructs a complete auxiliary symplectic plane, retains the protected physical space, decreases actual two-form cost, and gives a pure plane at equality.

**Limits / premises to retain:** Symmetric V, alternating nondegenerate Omega, realified uncertainty, Boolean mode basis, and dim E < 2*dim(Omega-orthogonal A). Equality is for the constructed plane.

[Frozen source, lines 20–34](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationSelection.lean#L20-L34)

```lean
open Module
namespace Gaussian.Phase
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem exists_bosonic_covariance_selection (V Ω : LinearMap.BilinForm ℝ E)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω) (A : Submodule ℝ E)
    (hExcess : finrank ℝ E < 2*finrank ℝ (Ω.orthogonal A))
    {n : ℕ} (e : Basis (Fin n × Bool) ℝ E) :
    ∃ P : Submodule ℝ E,
      finrank ℝ P = 2 ∧ P ≤ Ω.orthogonal A ∧ A ≤ Ω.orthogonal P ∧
      (Ω.restrict P).Nondegenerate ∧ (Ω.restrict (Ω.orthogonal P)).Nondegenerate ∧
      IsCompl P (Ω.orthogonal P) ∧ finrank ℝ (Ω.orthogonal P) = 2*(n-1) ∧
      ∃ eU : Basis (Fin (n-1) × Bool) ℝ (Ω.orthogonal P),
        bosonFormCost eU (V.restrict (Ω.orthogonal P)) (Ω.restrict (Ω.orthogonal P))
            (hV.restrict _) (fun x => hΩa x) ≤ bosonFormCost e V Ω hV hΩa ∧
        (bosonFormCost eU (V.restrict (Ω.orthogonal P)) (Ω.restrict (Ω.orthogonal P))
            (hV.restrict _) (fun x => hΩa x) = bosonFormCost e V Ω hV hΩa →
          ∃ p : PureCompatibleCovariance (Ω.restrict P), p.form = V.restrict P)
```

## B09

`Gaussian.Phase.BosonicAdaptationData.restricted_formCost_eq_half_spectrum`

**Paper node:** Section 3.2, actual retained spectrum.

**Reading and coverage:** The two restricted forms give half the real eigenvalue entropy sum of the genuine amplitude compression.

**Limits / premises to retain:** BosonicAdaptationData, alternating Omega, g<=V, J-invariant retained U and exact dimension/mode basis. No arbitrary-coordinate covariance-only spectrum shortcut.

[Frozen source, lines 32–36](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationCompression.lean#L32-L36)

```lean
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

theorem restricted_formCost_eq_half_spectrum (hΩ : Ω.IsAlt)
    (hLower : ∀ x, d.g x x ≤ V x x) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) {m : ℕ} (hm : finrank ℝ U = 2*m)
    (e : Basis (Fin m × Bool) ℝ U) :
    letI : NormedAddCommGroup E
```

## B10

`Gaussian.Phase.BosonicAdaptationData.restricted_formCost_rigidity`

**Paper node:** Lemma 3.1, bosonic equality.

**Reading and coverage:** Exact cost equality forces K=I on the true symplectic discarded complement and zero covariance cross block.

**Limits / premises to retain:** Retain BosonicAdaptationData, g<=V, alternating Omega, J-invariance, both mode bases and exact equality. No approximate-equality deletion.

[Frozen source, lines 49–55](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L49-L55)

```lean
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace BosonicAdaptationData
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)

theorem restricted_formCost_rigidity (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U)
    (he : bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) = bosonFormCost e V Ω d.covariance_symmetric hΩ) :
    (∀ x ∈ Ω.orthogonal U, d.K x = x) ∧
      (∀ x ∈ Ω.orthogonal U, ∀ y ∈ U, V x y = 0)
```

## B11

`Gaussian.Phase.PureCompatibleCovariance.exists_auxiliary_subcut_selection`

**Paper node:** Lemma 3.1 applied to AA-prime.

**Reading and coverage:** Selected one-mode plane inside the current auxiliary split has nonincreasing cost; equality supplies pure restricted covariance.

**Limits / premises to retain:** Pure full covariance, alternating physical/auxiliary forms, both cuts nondegenerate, dim A < dim S. This is the actual same-total deletion interface.

[Frozen source, lines 40–51](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationSubcuts.lean#L40-L51)

```lean
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

theorem exists_auxiliary_subcut_selection (p : PureCompatibleCovariance (productForm Ω σ))
    (hΩa : Ω.IsAlt) (hσa : σ.IsAlt) (A : Submodule ℝ E) (S : Submodule ℝ F)
    (hA : (Ω.restrict A).Nondegenerate) (hS : (σ.restrict S).Nondegenerate)
    (hExcess : finrank ℝ A < finrank ℝ S) :
    ∃ P : Submodule ℝ S, finrank ℝ P=2 ∧ ((σ.restrict S).restrict P).Nondegenerate ∧
      ((σ.restrict S).restrict ((σ.restrict S).orthogonal P)).Nondegenerate ∧
      IsCompl P ((σ.restrict S).orthogonal P) ∧
      finrank ℝ ((σ.restrict S).orthogonal P) = finrank ℝ S-2 ∧
      p.auxiliaryCutCost A (((σ.restrict S).orthogonal P).map S.subtype) ≤ p.auxiliaryCutCost A S ∧
      (p.auxiliaryCutCost A (((σ.restrict S).orthogonal P).map S.subtype) = p.auxiliaryCutCost A S →
        ∃ q : PureCompatibleCovariance ((σ.restrict S).restrict P),
          ∀ x y : P, q.form x y = p.form (0,(x : S)) (0,(y : S)))
```

## B12

`Gaussian.Phase.BosonicCovariancePurifier.exists_move_left`

**Paper node:** Section 5, transfer.

**Reading and coverage:** Produces an admissible same-total purifier with a one-unit side-count change and nonincreasing actual cost.

**Limits / premises to retain:** Raw feasible p, alternating physical Omega, nondegenerate physical A and dim A < 2*leftModes. The right move also requires Omega nondegenerate. This operation transfers, not deletes.

[Frozen source, lines 46–50](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMoves.lean#L46-L50)

```lean
universe u
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

theorem exists_move_left (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes+1=p.leftModes ∧ q.cost A ≤ p.cost A
```

## B13

`Gaussian.Phase.BosonicCovariancePurifier.exists_move_right`

**Paper node:** Section 5, transfer.

**Reading and coverage:** Produces an admissible same-total purifier with a one-unit side-count change and nonincreasing actual cost.

**Limits / premises to retain:** Raw feasible p, alternating physical Omega, nondegenerate physical A and dim(Omega-orthogonal A) < 2*rightModes. The right move also requires Omega nondegenerate. This operation transfers, not deletes.

[Frozen source, lines 71–76](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMoves.lean#L71-L76)

```lean
universe u
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

theorem exists_move_right (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ (Ω.orthogonal A) < 2*p.rightModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes=p.leftModes+1 ∧ q.cost A ≤ p.cost A
```

## B14

`Gaussian.Phase.PureCompatibleCovariance.invariant_auxiliary_of_subcut_pure`

**Paper node:** Section 5, pure marginal to globally deletable factor.

**Reading and coverage:** Pure covariance on the selected subcut makes its embedding invariant under the full pure generator.

**Limits / premises to retain:** Requires full PureCompatibleCovariance and exact agreement with the selected pure restriction. No assertion about arbitrary entropy-preserving deletions.

[Frozen source, lines 62–67](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationAuxDelete.lean#L62-L67)

```lean
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

theorem invariant_auxiliary_of_subcut_pure
    (p : PureCompatibleCovariance (productForm Ω σ)) (S : Submodule ℝ F) (T : Submodule ℝ S)
    (q : PureCompatibleCovariance ((σ.restrict S).restrict T))
    (hq : ∀ x y : T, q.form x y = p.form (0,(x : S)) (0,(y : S))) :
    ∀ x ∈ (T.map S.subtype).map (LinearMap.inr ℝ E F),
      p.generator x ∈ (T.map S.subtype).map (LinearMap.inr ℝ E F)
```

## B15

`Gaussian.Phase.BosonicCovariancePurifier.exists_delete_at_minimum`

**Paper node:** Section 5, one-mode removal.

**Reading and coverage:** An actual all-split fixed-total minimum at M+1 gives a feasible M-mode purifier at no greater cost.

**Limits / premises to retain:** Omega alternating/nondegenerate, nondegenerate A, dim E<=2*M and exact minimality against every same-total purifier. Handles excess on either side.

[Frozen source, lines 75–80](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainDelete.lean#L75-L80)

```lean
universe u
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}

theorem exists_delete_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ E ≤ 2*M)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A ≤ p.cost A
```

## B16

`Gaussian.Phase.exists_pure_covariance_auxiliary_equiv`

**Paper node:** Proposition 4.1 and Appendix A.

**Reading and coverage:** Two raw pure covariances with the same physical restriction and equal finite auxiliary dimension are related by an auxiliary form-preserving equivalence.

**Limits / premises to retain:** Finite real carriers, nondegenerate physical Omega, exact physical equality, pure-compatible covariances. Includes decoupled pure factors and zero dimensions; no inverse of a singular physical mixed block is assumed.

[Frozen source, lines 15–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationCrossOrbit.lean#L15-L24)

```lean
open Module
namespace Gaussian.Phase
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

theorem exists_pure_covariance_auxiliary_equiv
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (τ : LinearMap.BilinForm ℝ G) (hΩ : Ω.Nondegenerate)
    (p : PureCompatibleCovariance (productForm Ω σ))
    (q : PureCompatibleCovariance (productForm Ω τ))
    (hd : finrank ℝ F = finrank ℝ G)
    (hphys : ∀ x y, p.form (x,0) (y,0) = q.form (x,0) (y,0)) :
    ∃ Q : F ≃ₗ[ℝ] G,
      (∀ x y, τ (Q x) (Q y) = σ x y) ∧
      (∀ a b x y, q.form (a,Q x) (b,Q y) = p.form (a,x) (b,y))
```

## B17

`Gaussian.Phase.PureCompatibleCovariance.exists_auxiliarySubspaceCost_minimum`

**Paper node:** Section 4, fixed cut dimension.

**Reading and coverage:** At a fixed pure reference covariance the cost attains its minimum over all nondegenerate auxiliary subspaces of a given real dimension.

**Limits / premises to retain:** Requires nondegenerate physical A and an explicit feasible S0 of the prescribed dimension. No fixed-frame coordinate restriction or externally assumed compactness.

[Frozen source, lines 17–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationSubspaceMinimum.lean#L17-L24)

```lean
open Module
namespace Gaussian.Phase
namespace PureCompatibleCovariance
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}

theorem exists_auxiliarySubspaceCost_minimum
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (hA : (Ω.restrict A).Nondegenerate) {k : ℕ}
    (S₀ : Submodule ℝ F) (hd₀ : finrank ℝ S₀ = k)
    (hnd₀ : (σ.restrict S₀).Nondegenerate) :
    ∃ S : Submodule ℝ F, finrank ℝ S=k ∧ (σ.restrict S).Nondegenerate ∧
      ∀ T : Submodule ℝ F, finrank ℝ T=k → (σ.restrict T).Nondegenerate →
        p.auxiliaryCutCost A S ≤ p.auxiliaryCutCost A T
```

## B18

`Gaussian.Attainment.exists_bosonPairCost_minimum`

**Paper node:** Section 4, bosonic boundary exclusion.

**Reading and coverage:** Continuous covariance/form pairs on a compact parameter family admit an admissible minimum; inverse-form bounds are derived on a finite objective sublevel.

**Limits / premises to retain:** F compact, V and O continuous, every V on F positive definite, a feasible p0 with det O(p0)!=0. It does not assume all O are invertible or uniform squeezing bounds.

[Frozen source, lines 62–67](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Attainment/PairCompactness.lean#L62-L67)

```lean
open scoped Matrix ComplexOrder
namespace Gaussian.Attainment
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]

theorem exists_bosonPairCost_minimum (F : Set X) (hF : IsCompact F)
    (V O : X → HermitianMat ι ℂ) (hV : Continuous V) (hO : Continuous O)
    (hpos : ∀ p ∈ F, (V p).mat.PosDef)
    (p₀ : X) (hp₀ : p₀ ∈ F) (hO₀ : (O p₀).mat.det ≠ 0) :
    ∃ p ∈ F, (O p).mat.det ≠ 0 ∧
      ∀ q ∈ F, (O q).mat.det ≠ 0 → bosonPairCost (V p) (O p) ≤ bosonPairCost (V q) (O q)
```

## B19

`Gaussian.Phase.exists_bosonic_covariance_fixedTotal_minimum`

**Paper node:** Lemma 4.3, all fixed-total assignments.

**Reading and coverage:** An actual raw minimum against every purifier and every split at auxiliary total M.

**Limits / premises to retain:** Symmetric V, alternating/nondegenerate Omega, uncertainty, nondegenerate physical A, dim E<=2*M. Smaller feasible totals are handled by padding in the global proof.

[Frozen source, lines 17–23](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMinimum.lean#L17-L23)

```lean
universe u
open Module
namespace Gaussian.Phase
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem exists_bosonic_covariance_fixedTotal_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate) (M : ℕ)
    (hsize : finrank ℝ E ≤ 2*M) :
    ∃ p : BosonicCovariancePurifier V Ω M,
      ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A
```

## B20

`Gaussian.Phase.BosonicCovariancePurifier.pad_cost`

**Paper node:** Section 5, pure padding.

**Reading and coverage:** Padding from M to N preserves actual covariance cut cost.

**Limits / premises to retain:** Feasible raw p, M<=N, nondegenerate physical A. Pure padding is constructed; no infinite-mode limit is taken.

[Frozen source, lines 133–135](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationAuxPadding.lean#L133-L135)

```lean
universe u
open Module
namespace Gaussian.Phase
namespace BosonicCovariancePurifier
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
variable {H : Type u} [AddCommGroup H] [Module ℝ H] [FiniteDimensional ℝ H]
  {V Ω : LinearMap.BilinForm ℝ H} {M N : ℕ}

theorem pad_cost (p : BosonicCovariancePurifier V Ω M) (hMN : M≤N)
    (A : Submodule ℝ H) (hA : (Ω.restrict A).Nondegenerate) :
    (p.pad hMN).cost A = p.cost A
```

## B21

`Gaussian.Physical.Boson.IsGaussianWith.eq_product_of_cross_zero`

**Paper node:** Lemma 3.1, physical interpretation of the zero cross block.

**Reading and coverage:** Zero physical cross covariance for a Gaussian density gives exact factorization into its two actual reductions.

**Limits / premises to retain:** Requires Gaussianity and zero cross bilinear form on the specified product configuration. Supporting semantic theorem; this is not a direct extra hypothesis of B01.

[Frozen source, lines 50–56](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianFactorization.lean#L50-L56)

```lean
open MeasureTheory WithLp
namespace Gaussian.Physical.Boson
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem IsGaussianWith.eq_product_of_cross_zero
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V)
    (hcross : ∀ z : E×E,∀ w : F×F,V (leftPhaseEmbedding z) (rightPhaseEmbedding w)=0) :
    ρ=ρ.leftReduction.product ρ.rightReduction
```

## F02

`Gaussian.Physical.Fermion.realize_skew_contraction`

**Paper node:** Section 2 and Appendix C, covariance realization.

**Reading and coverage:** Every real skew contraction on the finite complete-mode coefficient space is the generator of an actual Wick density.

**Limits / premises to retain:** Skewness and norm contraction are explicit. Includes zero and pure endpoints; no nondegeneracy/inverse or occupation truncation.

[Frozen source, lines 62–65](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/RawRealization.lean#L62-L65)

```lean
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem realize_skew_contraction (n : ℕ)
    (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n) (hT : IsSkew T)
    (hBound : ∀ x,‖T x‖≤‖x‖) :
    ∃ ρ : Density n,IsQuasifree ρ ∧ covarianceGenerator ρ=T
```

## F03

`Gaussian.Physical.Fermion.quasifree_eq_of_generator`

**Paper node:** Section 2, state determined by covariance.

**Reading and coverage:** Equal trace-defined generators of two actual Wick densities imply equality of densities.

**Limits / premises to retain:** Both densities must satisfy IsQuasifree. Equality of covariance does not determine arbitrary non-Gaussian states.

[Frozen source, lines 76–78](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/RawRealization.lean#L76-L78)

```lean
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem quasifree_eq_of_generator {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (hT : covarianceGenerator ρ=covarianceGenerator σ) : ρ=σ
```

## F04

`Gaussian.Physical.Fermion.quasifree_entropy_of_covariance_normal_form`

**Paper node:** Section 2, entropy formula.

**Reading and coverage:** Genuine matrix entropy equals the sum of one-mode fermionic entropies for the actual covariance normal form.

**Limits / premises to retain:** IsQuasifree, each signed thermal t in [-1,1], an orthogonal R, and exact covariance pullback equality. A normal form is a proved input to this interface, not a guessed spectrum.

[Frozen source, lines 40–45](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/NormalFormBridge.lean#L40-L45)

```lean
open scoped BigOperators
namespace Gaussian.Physical.Fermion

theorem quasifree_entropy_of_covariance_normal_form (n : ℕ) (ρ : Density n)
    (hρ : IsQuasifree ρ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc (-1:ℝ) 1)
    (R : CoefficientSpace n ≃ₗᵢ[ℝ] CoefficientSpace n)
    (hΓ : ∀ a b, covariance ρ a b = covarianceForm (thermal n t ht)
      (R⁻¹ (coefficientBasis n a)) (R⁻¹ (coefficientBasis n b))) :
    Sᵥₙ ρ = ∑ i, Gaussian.Entropy.fermion (t i)
```

## F05

`Gaussian.Physical.Fermion.quasifree_pure_iff_covariancePure`

**Paper node:** Lemma 3.1 and Section 5, covariance/state purity.

**Reading and coverage:** Actual pure-state existence is equivalent to the trace-defined generator squaring to minus identity.

**Limits / premises to retain:** Requires IsQuasifree on the full finite occupation space. Not a general density-matrix covariance criterion.

[Frozen source, lines 59–60](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/PurityBridge.lean#L59-L60)

```lean
open Module Gaussian.Phase
open scoped Matrix RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem quasifree_pure_iff_covariancePure (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    (∃ ψ,ρ=MState.pure ψ) ↔ CovariancePure ρ
```

## F06

`Gaussian.Physical.Fermion.selectedRestriction_generator`

**Paper node:** Section 3.1, actual CAR restriction.

**Reading and coverage:** Generator of a genuine selected complete-mode restriction is the actual orthogonal compression.

**Limits / premises to retain:** Retain the implemented orthogonal action and its signed CAR unitary; an unsigned occupation permutation is insufficient.

[Frozen source, lines 44–51](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/SelectedCompression.lean#L44-L51)

```lean
open Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem selectedRestriction_generator (k l : ℕ) (ρ : Density (l+k))
    (R : CoefficientSpace (l+k) ≃ₗᵢ[ℝ] CoefficientSpace (l+k))
    (U : Matrix.unitaryGroup (Occupation (l+k)) ℂ) (hU : Implements (l+k) R U) :
    ∀ x,(selectedCoefficientEmbedding k l R).equivRange
        (covarianceGenerator (prefixRestriction k l (ρ.uConj U)) x) =
      compression (covarianceGenerator ρ)
        (selectedCoefficientEmbedding k l R).toLinearMap.range
        ((selectedCoefficientEmbedding k l R).equivRange x)
```

## F07

`Gaussian.Physical.Fermion.quasifree_entropy_comparison_of_compression`

**Paper node:** Lemma 3.1, fermionic inequality.

**Reading and coverage:** Actual entropy decreases under an adapted complete-mode compression.

**Limits / premises to retain:** Two Wick densities, SkewAdaptationData, J-invariant retained U, isometric coefficient identification, and exact generator-compression intertwining are all explicit.

[Frozen source, lines 68–74](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CompressionBridge.lean#L68-L74)

```lean
open Module Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem quasifree_entropy_comparison_of_compression {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (U : Submodule ℝ (CoefficientSpace n)) (hU : d.complexStructure.IsInvariant U)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] U)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) U (e x)) :
    Sᵥₙ σ ≤ Sᵥₙ ρ
```

## F08

`Gaussian.Physical.Fermion.quasifree_compression_entropy_rigidity`

**Paper node:** Lemma 3.1, fermionic equality.

**Reading and coverage:** Exact actual entropy equality forces K=I on the discarded orthogonal complement and zero cross block.

**Limits / premises to retain:** Retain both Wick predicates, adaptation, J-invariance, isometry, exact generator intertwining and exact entropy equality. No approximate rigidity.

[Frozen source, lines 12–19](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CompressionRigidity.lean#L12-L19)

```lean
open Module Gaussian.Phase Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem quasifree_compression_entropy_rigidity {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (V : Submodule ℝ (CoefficientSpace n)) (hV : d.complexStructure.IsInvariant V)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] V)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) V (e x))
    (he : Sᵥₙ σ=Sᵥₙ ρ) :
    (∀ x ∈ Vᗮ,d.K x=x) ∧ (∀ x ∈ Vᗮ,∀ y ∈ V,⟪d.K y,x⟫=0)
```

## F09

`Gaussian.Physical.Fermion.exists_counted_entropy_selection`

**Paper node:** Lemma 3.1, selected complete mode.

**Reading and coverage:** Constructs an implemented orthogonal action fixing all protected physical coefficients, with nonincreasing entropy and a pure selected terminal mode at equality.

**Limits / premises to retain:** A actual Density (1+k), IsQuasifree, and 2*a<1+k. This is c>a when 1+k=a+c. Does not claim a separately prescribed determinant or parity component.

[Frozen source, lines 26–36](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CountedCutSelection.lean#L26-L36)

```lean
open Module Gaussian.Phase
open scoped RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem exists_counted_entropy_selection (a k : ℕ) (hexcess : 2*a<1+k)
    (ρ : Density (1+k)) (hρ : IsQuasifree ρ) :
    ∃ R : CoefficientSpace (1+k) ≃ₗᵢ[ℝ] CoefficientSpace (1+k),
      ∃ U : Matrix.unitaryGroup (Occupation (1+k)) ℂ,
      Implements (1+k) R U ∧
      (∀ i : MajoranaIndex a,
        R (coefficientBasis (1+k) (Fin.castLE (by omega : a≤1+k) i.1,i.2)) =
          coefficientBasis (1+k) (Fin.castLE (by omega : a≤1+k) i.1,i.2)) ∧
      Sᵥₙ (prefixRestriction k 1 (ρ.uConj U)) ≤ Sᵥₙ ρ ∧
      (Sᵥₙ (prefixRestriction k 1 (ρ.uConj U))=Sᵥₙ ρ →
        ∃ ψ,suffixRestriction k 1 (ρ.uConj U)=MState.pure ψ)
```

## F10

`Gaussian.Physical.Fermion.exists_A_excess_transfer`

**Paper node:** Section 5, same-total A-prime to B-prime transfer.

**Reading and coverage:** Produces an actual competitor at counts (a,b+1) from (a+1,b), with entropy nonincrease and a pure terminal marginal at exact equality.

**Limits / premises to retain:** nA<a+1 and actual IsSidewisePurifier. Exact physical density is preserved, both parity components allowed; terminal purity is for this constructed state.

[Frozen source, lines 14–20](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AExcessTransfer.lean#L14-L20)

```lean
namespace Gaussian.Physical.Fermion

theorem exists_A_excess_transfer (nA nB a b : ℕ) (hexcess : nA<a+1)
    (ρ : Density (nA+nB)) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB (a+1) b ρ σ) :
    ∃ τ : Density ((a+(b+1))+(nA+nB)),IsSidewisePurifier nA nB a (b+1) ρ τ ∧
      sidewiseEntropy nA nB a (b+1) τ≤sidewiseEntropy nA nB (a+1) b σ ∧
      (sidewiseEntropy nA nB a (b+1) τ=sidewiseEntropy nA nB (a+1) b σ →
        ∃ ψ,suffixRestriction ((a+b)+(nA+nB)) 1 (modeCountCast (by omega) τ)=MState.pure ψ)
```

## F11

`Gaussian.Physical.Fermion.exists_B_excess_transfer`

**Paper node:** Section 5, opposite transfer.

**Reading and coverage:** Produces an actual competitor at counts (a+1,b) from (a,b+1) with nonincreasing cut entropy.

**Limits / premises to retain:** nB<b+1 and actual IsSidewisePurifier. The statement supplies a transfer; its conclusion does not include an equality-purity callback.

[Frozen source, lines 11–16](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/BExcessTransfer.lean#L11-L16)

```lean
namespace Gaussian.Physical.Fermion

theorem exists_B_excess_transfer (nA nB a b : ℕ) (hexcess : nB<b+1)
    (ρ : Density (nA+nB)) (σ : Density ((a+(b+1))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB a (b+1) ρ σ) :
    ∃ τ : Density (((a+1)+b)+(nA+nB)),
      IsSidewisePurifier nA nB (a+1) b ρ τ ∧
      sidewiseEntropy nA nB (a+1) b τ≤sidewiseEntropy nA nB a (b+1) σ
```

## F12

`Gaussian.Physical.Fermion.exists_sidewise_pure_B_entropy_deletion`

**Paper node:** Section 5, global pure-mode removal.

**Reading and coverage:** Deletes an explicitly pure terminal B-prime suffix while retaining an actual purifier and exactly the same AA-prime entropy.

**Limits / premises to retain:** IsSidewisePurifier and CovariancePure of the specified actual suffix after count cast. Arbitrary extra>=0; does not infer purity from an unrelated entropy equality.

[Frozen source, lines 69–75](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/PureDeletion.lean#L69-L75)

```lean
open scoped MState
namespace Gaussian.Physical.Fermion

theorem exists_sidewise_pure_B_entropy_deletion (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+(mB+extra))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA (mB+extra) ρ σ)
    (hs : CovariancePure (suffixRestriction ((mA+mB)+(nA+nB)) extra
      (modeCountCast (by omega) σ))) :
    ∃ τ : Density ((mA+mB)+(nA+nB)),IsSidewisePurifier nA nB mA mB ρ τ ∧
      sidewiseEntropy nA nB mA mB τ=sidewiseEntropy nA nB mA (mB+extra) σ
```

## F13

`Gaussian.Physical.Fermion.isCompact_quasifreePurifiers`

**Paper node:** Section 4, fermionic attainment.

**Reading and coverage:** The actual fixed-marginal pure Wick density domain is compact.

**Limits / premises to retain:** Finite k,l and actual Density k. Compactness permits an empty domain; a minimum additionally requires nonemptiness. This uses density-space compactness rather than literally the paper orbit proof.

[Frozen source, lines 62–63](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/StateTopology.lean#L62-L63)

```lean
open scoped Matrix BigOperators RealInnerProductSpace
namespace Gaussian.Physical.Fermion

theorem isCompact_quasifreePurifiers (k l : ℕ) (ρ : Density k) :
    IsCompact {σ : Density (l+k) | IsPureQuasifree σ ∧ prefixRestriction k l σ=ρ}
```

## F14

`Gaussian.Physical.Fermion.exists_finiteTotal_minimum`

**Paper node:** Lemma 4.3, fixed-total minimization.

**Reading and coverage:** Chooses an actual minimum simultaneously over all M+1 splits and all actual purifiers.

**Limits / premises to retain:** Explicit nonempty pure Wick fixed-prefix class at M; no assumption that every smaller M is feasible.

[Frozen source, lines 19–25](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotal.lean#L19-L25)

```lean
namespace Gaussian.Physical.Fermion

theorem exists_finiteTotal_minimum (nA nB M : ℕ) (ρ : Density (nA+nB))
    (hne : ∃ σ : Density (M+(nA+nB)),IsPureQuasifree σ ∧ prefixRestriction (nA+nB) M σ=ρ) :
    ∃ (j : Fin (M+1)) (σ : Density (M+(nA+nB))),
      IsPureQuasifree σ ∧ prefixRestriction (nA+nB) M σ=ρ ∧
      ∀ (i : Fin (M+1)) (τ : Density (M+(nA+nB))),
        IsPureQuasifree τ → prefixRestriction (nA+nB) M τ=ρ →
        finiteTotalEntropy nA nB M j σ≤finiteTotalEntropy nA nB M i τ
```

## F15

`Gaussian.Physical.Fermion.finitePurifier_attainment`

**Paper node:** Lemma 4.3, feasibility discharged.

**Reading and coverage:** Constructed Gaussian purification and padding discharge nonemptiness, giving actual fixed-total attainment.

**Limits / premises to retain:** Input IsQuasifree and M>=nA+nB. No separately assumed minimum or covariance realization.

[Frozen source, lines 24–27](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotalDomain.lean#L24-L27)

```lean
namespace Gaussian.Physical.Fermion

theorem finitePurifier_attainment (nA nB : ℕ) (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ)
    (M : ℕ) (hM : nA+nB≤M) :
    ∃ p : FinitePurifier nA nB ρ M,
      ∀ x : FinitePurifier nA nB ρ M,finitePurifierCost nA nB ρ M p≤finitePurifierCost nA nB ρ M x
```

## F16

`Gaussian.Physical.Fermion.finitePurifier_optimal_delete`

**Paper node:** Section 5, deletion at exact optimum.

**Reading and coverage:** An actual M+1 fixed-total minimum reduces to a feasible M-mode point with no greater cost, whichever side is excessive.

**Limits / premises to retain:** M>=nA+nB and exact comparison against every all-split FinitePurifier at M+1. Transfer precedes equality and removal.

[Frozen source, lines 41–46](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/OptimalDeletion.lean#L41-L46)

```lean
namespace Gaussian.Physical.Fermion

theorem finitePurifier_optimal_delete (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (hM : nA+nB≤M) (p : FinitePurifier nA nB ρ (M+1))
    (hp : ∀ x : FinitePurifier nA nB ρ (M+1),
      finitePurifierCost nA nB ρ (M+1) p≤finitePurifierCost nA nB ρ (M+1) x) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q≤finitePurifierCost nA nB ρ (M+1) p
```

## F17

`Gaussian.Physical.Fermion.finitePurifier_padding`

**Paper node:** Section 5, smaller-total competitors.

**Reading and coverage:** Every feasible point at M pads to L with exactly unchanged real entropy.

**Limits / premises to retain:** M<=L and an actual finite purifier. No purity, marginal or entropy equivalence is postulated without construction.

[Frozen source, lines 34–37](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotalPadding.lean#L34-L37)

```lean
namespace Gaussian.Physical.Fermion

theorem finitePurifier_padding (nA nB : ℕ) (ρ : Density (nA+nB)) (M L : ℕ) (hML : M≤L)
    (p : FinitePurifier nA nB ρ M) :
    ∃ q : FinitePurifier nA nB ρ L,
      finitePurifierCost nA nB ρ L q=finitePurifierCost nA nB ρ M p
```

## F18

`Gaussian.Physical.Fermion.finitePurifier_matchSplit`

**Paper node:** Section 5, sidewise matching.

**Reading and coverage:** At total nA+nB an actual finite purifier can be reallocated to counts (nA,nB) without raising entropy.

**Limits / premises to retain:** Requires an actual feasible p at that total. It need not already minimize, and the conclusion is nonincrease rather than equality; global minimality supplies equality when needed.

[Frozen source, lines 18–22](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/MatchedSplit.lean#L18-L22)

```lean
namespace Gaussian.Physical.Fermion

theorem finitePurifier_matchSplit (nA nB : ℕ) (ρ : Density (nA+nB))
    (p : FinitePurifier nA nB ρ (nA+nB)) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ≤finitePurifierCost nA nB ρ (nA+nB) p
```

## F19

`Gaussian.Physical.Fermion.pure_quasifree_has_definiteParity`

**Paper node:** Section 2 and Appendix B, main parity convention.

**Reading and coverage:** An actual pure Wick density has some definite total parity.

**Limits / premises to retain:** Existence of some parity does not prescribe which parity the matched optimizer has. Supporting scope theorem, not the optional fixed-parity strengthening.

[Frozen source, lines 67–68](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/DefiniteParity.lean#L67-L68)

```lean
open scoped Matrix
namespace Gaussian.Physical.Fermion

theorem pure_quasifree_has_definiteParity {n : ℕ} (ρ : Density n) (hρ : IsPureQuasifree ρ) :
    ∃ odd : Bool,HasParity ρ odd
```

## S01

`Gaussian.Entropy.boson_compression_comparison`

**Paper node:** Sections 3.1–3.2, interlacing/trace core.

**Reading and coverage:** Finite real self-adjoint compression entropy half-sum comparison.

**Limits / premises to retain:** Finite real inner-product space, true orthogonal compression U, exact full/retained dimension counts; K symmetric and K-I positive. This coefficient theorem alone has no physical state semantics; B09 or F07/F08 supply the bridge.

[Frozen source, lines 37–41](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Entropy/Compression.lean#L37-L41)

```lean
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

theorem boson_compression_comparison (hK : K.IsSymmetric)
    (hd : (K-LinearMap.id).IsPositive) (U : Submodule ℝ E)
    {m c : ℕ} (hn : Module.finrank ℝ E = m+c) (hm : Module.finrank ℝ U = m) :
    realListCost boson ((compression_symmetric hK U).eigenvalues hm) ≤
      realListCost boson (hK.eigenvalues hn)
```

## S02

`Gaussian.Entropy.fermion_compression_comparison`

**Paper node:** Sections 3.1–3.2, interlacing/trace core.

**Reading and coverage:** Finite real self-adjoint compression entropy half-sum comparison.

**Limits / premises to retain:** Finite real inner-product space, true orthogonal compression U, exact full/retained dimension counts; K positive and I-K positive. This coefficient theorem alone has no physical state semantics; B09 or F07/F08 supply the bridge.

[Frozen source, lines 47–51](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Entropy/Compression.lean#L47-L51)

```lean
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

theorem fermion_compression_comparison (hK : K.IsPositive)
    (hd : (LinearMap.id-K).IsPositive) (U : Submodule ℝ E)
    {c m : ℕ} (hn : Module.finrank ℝ E = c+m) (hm : Module.finrank ℝ U = m) :
    realListCost fermion ((compression_symmetric hK.isSymmetric U).eigenvalues hm) ≤
      realListCost fermion (hK.isSymmetric.eigenvalues hn)
```

## S03

`Gaussian.Entropy.boson_compression_rigidity`

**Paper node:** Sections 3.1–3.2, interlacing/trace core.

**Reading and coverage:** Finite real self-adjoint compression rigidity: endpoint identity and vanishing cross block.

**Limits / premises to retain:** Finite real inner-product space, true orthogonal compression U, exact full/retained dimension counts; K symmetric, K-I positive, exact half-sum equality. This coefficient theorem alone has no physical state semantics; B09 or F07/F08 supply the bridge.

[Frozen source, lines 63–68](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Entropy/Compression.lean#L63-L68)

```lean
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

theorem boson_compression_rigidity (hK : K.IsSymmetric)
    (hd : (K-LinearMap.id).IsPositive) (U : Submodule ℝ E)
    {m c : ℕ} (hn : Module.finrank ℝ E = m+c) (hm : Module.finrank ℝ U = m)
    (he : realListCost boson ((compression_symmetric hK U).eigenvalues hm) =
      realListCost boson (hK.eigenvalues hn)) :
    (∀ x ∈ Uᗮ, K x = x) ∧ (∀ x ∈ Uᗮ, ∀ y ∈ U, ⟪K y,x⟫ = 0)
```

## S04

`Gaussian.Entropy.fermion_compression_rigidity`

**Paper node:** Sections 3.1–3.2, interlacing/trace core.

**Reading and coverage:** Finite real self-adjoint compression rigidity: endpoint identity and vanishing cross block.

**Limits / premises to retain:** Finite real inner-product space, true orthogonal compression U, exact full/retained dimension counts; K positive, I-K positive, exact half-sum equality. This coefficient theorem alone has no physical state semantics; B09 or F07/F08 supply the bridge.

[Frozen source, lines 85–90](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Entropy/Compression.lean#L85-L90)

```lean
open scoped RealInnerProductSpace
open Gaussian.Spectral
namespace Gaussian.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {K : E →ₗ[ℝ] E}

theorem fermion_compression_rigidity (hK : K.IsPositive)
    (hd : (LinearMap.id-K).IsPositive) (U : Submodule ℝ E)
    {c m : ℕ} (hn : Module.finrank ℝ E = c+m) (hm : Module.finrank ℝ U = m)
    (he : realListCost fermion ((compression_symmetric hK.isSymmetric U).eigenvalues hm) =
      realListCost fermion (hK.isSymmetric.eigenvalues hn)) :
    (∀ x ∈ Uᗮ, K x = x) ∧ (∀ x ∈ Uᗮ, ∀ y ∈ U, ⟪K y,x⟫ = 0)
```

## G01

`Gaussian.Optimization.global_attained_from_optimal_deletion`

**Paper node:** Section 5, induction over all finite totals.

**Reading and coverage:** An actual n-total witness beats every feasible finite-total point, including totals below n.

**Limits / premises to retain:** Three explicit premises: exact attainment for all M>=n, deletion only at an attained M+1 optimum, and padding from each M<n to n. A generic theorem; sector-specific discharges B19/B15/B20 or F15/F16/F17 are mandatory.

[Frozen source, lines 13–20](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Optimization/FiniteDescent.lean#L13-L20)

```lean
namespace Gaussian.Optimization

theorem global_attained_from_optimal_deletion
    (E : ℕ → Type*) (cost : ∀ M, E M → ℝ) (n : ℕ)
    (attain : ∀ M, n ≤ M → ∃ p : E M, ∀ x : E M, cost M p ≤ cost M x)
    (delete : ∀ M, n ≤ M → ∀ p : E (M+1),
      (∀ x : E (M+1), cost (M+1) p ≤ cost (M+1) x) →
      ∃ q : E M, cost M q ≤ cost (M+1) p)
    (pad : ∀ M, M < n → ∀ x : E M, ∃ y : E n, cost n y ≤ cost M x) :
    ∃ p : E n, ∀ M, ∀ x : E M, cost n p ≤ cost M x
```

## G02

`Gaussian.Optimization.exists_matched_cost_le_of_unit_moves`

**Paper node:** Section 5, terminating split reallocation.

**Reading and coverage:** Finite iteration reaches a specified natural index at nonincreasing cost.

**Limits / premises to retain:** Every point below target admits a +1 move, every point above target admits a -1 move, each nonincreasing. It does not independently prove admissibility, compactness or a global optimum.

[Frozen source, lines 10–14](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Optimization/MatchedIteration.lean#L10-L14)

```lean
namespace Gaussian.Optimization

theorem exists_matched_cost_le_of_unit_moves {E : Type*} (index : E → ℕ)
    (cost : E → ℝ) (target : ℕ)
    (up : ∀ x,index x<target → ∃ y,index y=index x+1 ∧ cost y≤cost x)
    (down : ∀ x,target < index x → ∃ y,index y+1=index x ∧ cost y≤cost x)
    (x : E) : ∃ y,index y=target ∧ cost y≤cost x
```

## D14

`Gaussian.Physical.Boson.NormalDensity`

**Paper node:** Section 2, normal bosonic state.

**Reading and coverage:** Positive trace-class operator of trace one on the full complete complex Hilbert space.

**Limits / premises to retain:** Schrodinger E is the full L2 space in B01, not a finite Fock cutoff. Gaussianity is a separate raw predicate.

[Frozen source, lines 31–35](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/NormalDensity.lean#L31-L35)

```lean
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
namespace Gaussian.Physical.Boson
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure NormalDensity (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : TraceClass H
  nonneg : 0 ≤ operator.1
  trace_one : normalTrace operator = 1
```

## D15

`Gaussian.Physical.Boson.NormalDensity.entropy`

**Paper node:** Section 2, von Neumann entropy.

**Reading and coverage:** Trace norm of the positive CFC -rho log rho operator if trace class, otherwise infinity.

**Limits / premises to retain:** Defined on arbitrary normal densities before a Gaussian spectrum is identified. B03 separately proves finiteness and the cost equality.

[Frozen source, lines 43–45](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/NormalEntropy.lean#L43-L45)

```lean
open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace ENNReal
namespace Gaussian.Physical.Boson
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def NormalDensity.entropy (ρ : NormalDensity H) : ℝ≥0∞ := by
  classical
  exact if h : IsTraceClass ρ.entropyOperator then ENNReal.ofReal (traceNorm ρ.entropyOperator h) else ∞
```

## D16

`Gaussian.Covariance.RealifiedUncertainty`

**Paper node:** Section 2, V+i*Omega positive semidefinite.

**Reading and coverage:** Positivity of the complex uncertainty quadratic form written using real coefficient vectors.

**Limits / premises to retain:** V symmetry and Omega alternation/nondegeneracy are separate premises when needed. Sign conventions are equivalent because the second vector ranges freely.

[Frozen source, lines 13–14](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Covariance/Uncertainty.lean#L13-L14)

```lean
namespace Gaussian.Covariance
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def RealifiedUncertainty (V Ω : LinearMap.BilinForm ℝ E) : Prop :=
  ∀ x y, 0 ≤ V x x + V y y - 2 * Ω x y
```
