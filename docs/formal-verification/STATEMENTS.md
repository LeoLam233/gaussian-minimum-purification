# Exact Lean statement dossier

Companion to [the expert appendix](APPENDIX.md), version 1.0.0 (2026-10-13). These are verbatim source **statement headers**, not elaborated `#print` output. The source links and SHA-256 values bind the excerpts to Lean v0.1.3. Ambient `variable` commands shown in source order may include unused variables and repetitions; Lean elaboration determines which enter a declaration. Imports, instances and definitions are read from the linked module. Use `#print` in the pinned environment for fully elaborated binders. Proof bodies remain in their original source files. This dossier is a navigational extract, not another proof or an independent audit.


## B01

`Gaussian.Physical.Boson.exists_matched_global_gaussian_purification`

Paper: Theorem 2.1. [Frozen source, lines 17–23](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GlobalMinimum.lean#L17-L23).

Hypotheses: nA,nB : ℕ; ρ : BipartiteDensity nA nB; IsGaussian ρ.

Coverage and boundary: Actual matched pure Gaussian witness; finite ENNReal entropy, equality to all-finite infimum, comparison with every finite pair. No non-Gaussian comparison.

Module SHA-256: `9ce7acc288cd0c2ab8afb895e1cc58b564dd820727cf0ebb8d4d4ea6ab09b82f`.


Statement header:

```lean
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

Paper: Theorem 2.1. [Frozen source, lines 14–21](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/GlobalMinimum.lean#L14-L21).

Hypotheses: nA,nB : ℕ; ρ : Density (nA+nB); IsQuasifree ρ.

Coverage and boundary: Actual matched pure Wick density; real entropy equals all-finite infimum, comparison with every finite pair. Both parity components; no prescribed-parity conclusion.

Module SHA-256: `cb655382c53e16ac6c18a2512ebc86a3c7f40db1c403fa04ddc00e3074581942`.


Statement header:

```lean
theorem exists_matched_global_gaussian_purification (nA nB : ℕ)
    (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ=gaussianPurificationInfimum nA nB ρ ∧
      ∀ (mA mB : ℕ) (τ : Density ((mA+mB)+(nA+nB))),
        IsSidewisePurifier nA nB mA mB ρ τ →
          sidewiseEntropy nA nB nA nB σ≤sidewiseEntropy nA nB mA mB τ
```


## B02

`Gaussian.Physical.Boson.existsUnique_gaussian_iff`

Paper: §2 covariance conventions; semantic input. [Frozen source, lines 14–16](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianEntropyObjective.lean#L14-L16).

Hypotheses: Finite real configuration Hilbert space with Borel measurable structure; arbitrary finite linear mean m and real bilinear V.

Coverage and boundary: Realizability and uniqueness iff V symmetric and RealifiedUncertainty. No nonnormal or infinite-mode representation.

Module SHA-256: `bf2870a67787cd7f862c86719fabd26217d3f6fc07921452d6b53f11380780da`.


Ambient source variables:

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
```


Statement header:

```lean
theorem existsUnique_gaussian_iff (m : (E×E) →ₗ[ℝ] ℝ) (V : LinearMap.BilinForm ℝ (E×E)) :
    (∃! ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ m V) ↔
      V.IsSymm ∧ Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E)
```


## B03

`Gaussian.Physical.Boson.IsGaussianWith.entropy_objective`

Paper: §2 entropy formula. [Frozen source, lines 26–31](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianEntropyObjective.lean#L26-L31).

Hypotheses: Same configuration assumptions; finite index type and basis e of E×E; actual density with IsGaussianWith ρ m V.

Coverage and boundary: Proves entropy ≠ top before toReal equals bosonFormCost. Not an entropy identity for arbitrary densities.

Module SHA-256: `bf2870a67787cd7f862c86719fabd26217d3f6fc07921452d6b53f11380780da`.


Ambient source variables:

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
```


Statement header:

```lean
theorem IsGaussianWith.entropy_objective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.entropy≠⊤ ∧ ρ.entropy.toReal=
      bosonFormCost e V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt
```


## B04

`Gaussian.Physical.Boson.IsGaussianWith.isPure_iff_exists_pureCompatible`

Paper: §2 pure covariance semantics. [Frozen source, lines 75–78](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianPurity.lean#L75-L78).

Hypotheses: Same configuration assumptions; actual IsGaussianWith ρ m V.

Coverage and boundary: Pure actual state iff compatible pure covariance with form V; Gaussianity required.

Module SHA-256: `7539255c5274899b6021ead69b648d8f3ec1ed882b89de3b0339a1cbb5f07157`.


Ambient source variables:

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
```


Statement header:

```lean
theorem IsGaussianWith.isPure_iff_exists_pureCompatible {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.IsPure ↔ ∃ d : PureCompatibleCovariance (weylSymplecticForm E), d.form=V
```


## B05

`Gaussian.Physical.Boson.IsGaussianWith.sidewiseReduction`

Paper: §2 actual subsystem semantics. [Frozen source, lines 51–57](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/SidewiseDomain.lean#L51-L57).

Hypotheses: Finite configurations A,B,C,D; actual four-party IsGaussianWith σ m V.

Coverage and boundary: True AA′ reduction has restricted mean and covariance; complete subsystem, not arbitrary coefficient deletion.

Module SHA-256: `34ecd522db762c9c93859845be00489ccd1f5b4e33a9d9cdd73c135ff0923b6b`.


Ambient source variables:

```lean
variable {A B C D : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
```


Statement header:

```lean
theorem IsGaussianWith.sidewiseReduction
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    {m : (FourConfiguration A B C D×FourConfiguration A B C D) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (FourConfiguration A B C D×FourConfiguration A B C D)}
    (hσ : IsGaussianWith σ m V) :
    IsGaussianWith (sidewiseReduction σ) (m.comp sidewisePhaseEmbedding)
      (V.compl₁₂ sidewisePhaseEmbedding sidewisePhaseEmbedding)
```


## B06

`Gaussian.Physical.Boson.IsSidewisePurifier.exists_covariancePurifier`

Paper: Theorem 2.1 comparison domain. [Frozen source, lines 23–32](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/CovarianceDomainBridge.lean#L23-L32).

Hypotheses: Finite configurations A,B,C,D; input IsGaussianWith ρ m V; σ an actual IsSidewisePurifier of ρ.

Coverage and boundary: Every actual competitor yields raw covariance purifier, exact two counts and finite equal cost. Essential converse direction; no bound on competitor counts.

Module SHA-256: `b980a8a3b83c172560af0693c1ae20a040db227bf7b2c1a34e43d914e5b2167a`.


Ambient source variables:

```lean
variable {A B C D : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
```


Statement header:

```lean
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


## B07

`Gaussian.Physical.Boson.covariancePurifier_exists_sidewise_realization`

Paper: Theorem 2.1 witness realization. [Frozen source, lines 15–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/CovarianceDomainRealization.lean#L15-L24).

Hypotheses: Finite A,B; input IsGaussianWith ρ m V; M : ℕ; raw BosonicCovariancePurifier V Ω M for the Weyl form.

Coverage and boundary: Actual purifier with exact side counts and cost; physical mean preserved. Does not assert unique optimizer.

Module SHA-256: `fc8b2148620fe1d61d83305d0a41b149d3ddcd4d3ddef10c47548ba8ed29cd95`.


Ambient source variables:

```lean
variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [MeasurableSpace B] [BorelSpace B]
```


Statement header:

```lean
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


## B08

`Gaussian.Phase.exists_bosonic_product_selection`

Paper: Lemma 3.1, §3.2. [Frozen source, lines 31–47](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationProductSelection.lean#L31-L47).

Hypotheses: Finite real modules E,F; symmetric V on E×F; alternating nondegenerate Ω,σ; product uncertainty; finrank E < finrank F.

Coverage and boundary: Selected auxiliary plane, symplectic complement, nonincrease, equality implies pure plane covariance. Covariance statement, not standalone physical factorization iff.

Module SHA-256: `bf2f45fb18e290b6a5d0da643c54e4a79d9f3abae821e4497bec4525111c4db3`.


Ambient source variables:

```lean
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
```


Statement header:

```lean
theorem exists_bosonic_product_selection (V : LinearMap.BilinForm ℝ (E × F))
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (hV : V.IsSymm) (hΩa : Ω.IsAlt) (hσa : σ.IsAlt)
    (hΩn : Ω.Nondegenerate) (hσn : σ.Nondegenerate)
    (hUnc : Gaussian.Covariance.RealifiedUncertainty V (productForm Ω σ))
    (hExcess : finrank ℝ E < finrank ℝ F) :
    ∃ P : Submodule ℝ F, finrank ℝ P=2 ∧ (σ.restrict P).Nondegenerate ∧
      (σ.restrict (σ.orthogonal P)).Nondegenerate ∧ IsCompl P (σ.orthogonal P) ∧
      finrank ℝ (σ.orthogonal P) = finrank ℝ F-2 ∧
      productRestrictionCost V Ω σ hV hΩa hσa (σ.orthogonal P) ≤
        bosonFormCost (Module.finBasis ℝ (E × F)) V (productForm Ω σ) hV
          (productForm_alternating hΩa hσa) ∧
      (productRestrictionCost V Ω σ hV hΩa hσa (σ.orthogonal P) =
          bosonFormCost (Module.finBasis ℝ (E × F)) V (productForm Ω σ) hV
            (productForm_alternating hΩa hσa) →
        ∃ p : PureCompatibleCovariance (σ.restrict P),
          ∀ x y : P, p.form x y = V (0,x) (0,y))
```


## B09

`Gaussian.Phase.BosonicAdaptationData.restricted_formCost_eq_half_spectrum`

Paper: §3.2 actual restricted spectrum. [Frozen source, lines 32–41](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationCompression.lean#L32-L41).

Hypotheses: BosonicAdaptationData d for V,Ω; Ω alternating; g ≤ V as quadratic forms; U J-invariant; dim U=2m; mode basis e.

Coverage and boundary: Both restricted forms equal genuine adapted-metric compression cost. U need not be K-invariant; arbitrary non-J-invariant U excluded.

Module SHA-256: `ede9680db2e504ab20ddbbf3593caafcc78b04bfeea0f4ed11cb81b4822ce930`.


Ambient source variables:

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)
```


Statement header:

```lean
theorem restricted_formCost_eq_half_spectrum (hΩ : Ω.IsAlt)
    (hLower : ∀ x, d.g x x ≤ V x x) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) {m : ℕ} (hm : finrank ℝ U = 2*m)
    (e : Basis (Fin m × Bool) ℝ U) :
    letI : NormedAddCommGroup E := d.metricCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore d.metricCore.toCore
    bosonFormCost e (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) =
      Gaussian.Entropy.realListCost Gaussian.Entropy.boson
        ((compression_symmetric (show d.K.IsSymmetric from d.amplitude_symm) U).eigenvalues hm)
```


## B10

`Gaussian.Phase.BosonicAdaptationData.restricted_formCost_le`

Paper: Lemma 3.1 inequality. [Frozen source, lines 27–31](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L27-L31).

Hypotheses: Finite real module; adaptation d; alternating Ω; g≤V; J-invariant U; full and retained Boolean mode bases.

Coverage and boundary: Covariance cost comparison. Actual entropy needs B03 and subsystem bridges.

Module SHA-256: `8d6ddfb4feaeb534c577eaf2e74856a7b5ed4ea1cdd33fad631e6f03ce0b0af0`.


Ambient source variables:

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)
```


Statement header:

```lean
theorem restricted_formCost_le (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U) :
    bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) ≤ bosonFormCost e V Ω d.covariance_symmetric hΩ
```


## B11

`Gaussian.Phase.BosonicAdaptationData.restricted_formCost_rigidity`

Paper: Lemma 3.1 equality. [Frozen source, lines 49–55](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L49-L55).

Hypotheses: B10 hypotheses plus exact equality of the two form costs.

Coverage and boundary: K=I on true symplectic complement and zero V cross block. Approximate equality and arbitrary deletion excluded.

Module SHA-256: `8d6ddfb4feaeb534c577eaf2e74856a7b5ed4ea1cdd33fad631e6f03ce0b0af0`.


Ambient source variables:

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)
```


Statement header:

```lean
theorem restricted_formCost_rigidity (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U)
    (he : bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) = bosonFormCost e V Ω d.covariance_symmetric hΩ) :
    (∀ x ∈ Ω.orthogonal U, d.K x = x) ∧
      (∀ x ∈ Ω.orthogonal U, ∀ y ∈ U, V x y = 0)
```


## B12

`Gaussian.Phase.BosonicAdaptationData.exists_pure_discarded_of_formCost_eq`

Paper: Lemma 3.1 pure endpoint. [Frozen source, lines 103–110](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L103-L110).

Hypotheses: B10 hypotheses plus exact cost equality.

Coverage and boundary: Constructs PureCompatibleCovariance on the discarded complement; physical realization is separate.

Module SHA-256: `8d6ddfb4feaeb534c577eaf2e74856a7b5ed4ea1cdd33fad631e6f03ce0b0af0`.


Ambient source variables:

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} (d : BosonicAdaptationData V Ω)
```


Statement header:

```lean
theorem exists_pure_discarded_of_formCost_eq (hΩ : Ω.IsAlt)
    (hLower : ∀ x, d.g x x ≤ V x x) (U : Submodule ℝ E)
    (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U)
    (he : bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) = bosonFormCost e V Ω d.covariance_symmetric hΩ) :
    ∃ p : PureCompatibleCovariance (Ω.restrict (Ω.orthogonal U)),
      p.form = V.restrict (Ω.orthogonal U)
```


## F02

`Gaussian.Physical.Fermion.realize_skew_contraction`

Paper: §2 and Appendix A normal-form semantics. [Frozen source, lines 62–65](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/RawRealization.lean#L62-L65).

Hypotheses: n : ℕ; real coefficient generator T skew symmetric and ‖T x‖≤‖x‖ for every x.

Coverage and boundary: Actual Wick density realizes raw contraction; no non-quasifree Gaussianity claim.

Module SHA-256: `6880ce86df81f7e292556d781efa7f0b479de81e5fe9ee0b751b806a45af7fba`.


Statement header:

```lean
theorem realize_skew_contraction (n : ℕ)
    (T : CoefficientSpace n →ₗ[ℝ] CoefficientSpace n) (hT : IsSkew T)
    (hBound : ∀ x,‖T x‖≤‖x‖) :
    ∃ ρ : Density n,IsQuasifree ρ ∧ covarianceGenerator ρ=T
```


## F03

`Gaussian.Physical.Fermion.quasifree_eq_of_generator`

Paper: §3.1 covariance determines state. [Frozen source, lines 76–78](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/RawRealization.lean#L76-L78).

Hypotheses: Two actual quasifree densities of the same size; identical covariance generators.

Coverage and boundary: Equality of densities, using complete word span; covariance alone insufficient outside Wick class.

Module SHA-256: `6880ce86df81f7e292556d781efa7f0b479de81e5fe9ee0b751b806a45af7fba`.


Statement header:

```lean
theorem quasifree_eq_of_generator {n : ℕ} (ρ σ : Density n)
    (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (hT : covarianceGenerator ρ=covarianceGenerator σ) : ρ=σ
```


## F04

`Gaussian.Physical.Fermion.quasifree_entropy_eq_hermitianCost`

Paper: §2 entropy formula. [Frozen source, lines 92–93](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/OrthogonalSpectrum.lean#L92-L93).

Hypotheses: n : ℕ; ρ : Density n; IsQuasifree ρ.

Coverage and boundary: Actual von Neumann entropy equals covariance Hermitian cost; includes zero/repeated/pure endpoints.

Module SHA-256: `e8c92709fbcc790be0a490f3d7bd786ea9e48071c47bd5f2e1392f0ea3da087d`.


Statement header:

```lean
theorem quasifree_entropy_eq_hermitianCost (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    Sᵥₙ ρ = Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat ρ)
```


## F05

`Gaussian.Physical.Fermion.quasifree_pure_iff_covariancePure`

Paper: §3.1 pure endpoint. [Frozen source, lines 59–60](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/PurityBridge.lean#L59-L60).

Hypotheses: n : ℕ; actual density ρ; IsQuasifree ρ.

Coverage and boundary: Pure vector density iff generator squares to −I. No chosen total parity.

Module SHA-256: `592227061756479031f1b8718d588be5985071a6574a1fb182687d7a4ca166b2`.


Statement header:

```lean
theorem quasifree_pure_iff_covariancePure (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    (∃ ψ,ρ=MState.pure ψ) ↔ CovariancePure ρ
```


## F06

`Gaussian.Physical.Fermion.quasifree_entropy_comparison_of_compression`

Paper: Lemma 3.1, §3.1. [Frozen source, lines 68–74](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CompressionBridge.lean#L68-L74).

Hypotheses: Actual quasifree ρ,σ; skew adaptation d; invariant retained V; isometry e to V; exact compressed-generator intertwining hT.

Coverage and boundary: Entropy comparison for actual states once subsystem generator is identified. Not every deletion satisfies hT or invariance.

Module SHA-256: `5f18862890486e4fb3fa13fa22e2efe8930138fc8625732f84b603a7bf6e5e46`.


Statement header:

```lean
theorem quasifree_entropy_comparison_of_compression {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (U : Submodule ℝ (CoefficientSpace n)) (hU : d.complexStructure.IsInvariant U)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] U)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) U (e x)) :
    Sᵥₙ σ ≤ Sᵥₙ ρ
```


## F07

`Gaussian.Physical.Fermion.quasifree_compression_entropy_rigidity`

Paper: Lemma 3.1 equality. [Frozen source, lines 12–19](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CompressionRigidity.lean#L12-L19).

Hypotheses: F06 hypotheses plus exact equality Sᵥₙ σ=Sᵥₙ ρ.

Coverage and boundary: K=I on discarded orthogonal complement and zero K cross block; no approximate rigidity.

Module SHA-256: `1b276016e8e05f340d8abd212365d383c2870ef53c3b03dcdca1e90421446269`.


Statement header:

```lean
theorem quasifree_compression_entropy_rigidity {n k : ℕ}
    (ρ : Density n) (σ : Density k) (hρ : IsQuasifree ρ) (hσ : IsQuasifree σ)
    (d : SkewAdaptationData (covarianceGenerator ρ))
    (V : Submodule ℝ (CoefficientSpace n)) (hV : d.complexStructure.IsInvariant V)
    (e : CoefficientSpace k ≃ₗᵢ[ℝ] V)
    (hT : ∀ x,e (covarianceGenerator σ x)=compression (covarianceGenerator ρ) V (e x))
    (he : Sᵥₙ σ=Sᵥₙ ρ) :
    (∀ x ∈ Vᗮ,d.K x=x) ∧ (∀ x ∈ Vᗮ,∀ y ∈ V,⟪d.K y,x⟫=0)
```


## F08

`Gaussian.Physical.Fermion.exists_counted_entropy_selection`

Paper: Lemma 3.1 selected local mode. [Frozen source, lines 26–36](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/CountedCutSelection.lean#L26-L36).

Hypotheses: a,k : ℕ; 2*a<1+k; ρ : Density (1+k); IsQuasifree ρ.

Coverage and boundary: Constructs implemented orthogonal action fixing a protected complete modes; restriction lowers entropy, equality implies actual pure suffix. Inequality is strict excess c>a with c=1+k−a.

Module SHA-256: `80b49986024ecd80eb72813e196c4be78149ea7072cef6cb05ad0244d7b7451f`.


Statement header:

```lean
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


## B13

`Gaussian.Phase.exists_pure_covariance_auxiliary_equiv`

Paper: Proposition 4.1 and Appendix A. [Frozen source, lines 15–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationCrossOrbit.lean#L15-L24).

Hypotheses: Finite real E,F,G; Ω nondegenerate; two compatible pure covariances for product forms; equal auxiliary dimensions and identical physical covariance.

Coverage and boundary: Actual auxiliary symplectic equivalence of whole covariances, including uncoupled pure factors. Covariance orbit, not a separately named physical-unitary orbit theorem.

Module SHA-256: `672e8182ee92c2388f7aeb422d3d06b6b5c3410e508f49122dbebfc338c38181`.


Ambient source variables:

```lean
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
```


Statement header:

```lean
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


## B14

`Gaussian.Phase.PureCompatibleCovariance.exists_auxiliarySubspaceCost_minimum`

Paper: Proposition 4.2 and Lemma 4.3. [Frozen source, lines 17–24](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationSubspaceMinimum.lean#L17-L24).

Hypotheses: Finite real E,F; compatible pure p; nondegenerate physical A; existing k-dimensional nondegenerate auxiliary cut S₀.

Coverage and boundary: Attains minimum over every nondegenerate cut of that dimension. Does not assume compactness of the open symplectic-cut locus.

Module SHA-256: `df6014f3fece83c024234d2be23cf803810019c8cd9cdeca06e7192eec5854bc`.


Ambient source variables:

```lean
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
```


Statement header:

```lean
theorem exists_auxiliarySubspaceCost_minimum
    (p : PureCompatibleCovariance (productForm Ω σ)) (A : Submodule ℝ E)
    (hA : (Ω.restrict A).Nondegenerate) {k : ℕ}
    (S₀ : Submodule ℝ F) (hd₀ : finrank ℝ S₀ = k)
    (hnd₀ : (σ.restrict S₀).Nondegenerate) :
    ∃ S : Submodule ℝ F, finrank ℝ S=k ∧ (σ.restrict S).Nondegenerate ∧
      ∀ T : Submodule ℝ F, finrank ℝ T=k → (σ.restrict T).Nondegenerate →
        p.auxiliaryCutCost A S ≤ p.auxiliaryCutCost A T
```


## B15

`Gaussian.Attainment.exists_bosonPairCost_minimum`

Paper: Lemma 4.3, §4 boundary estimate. [Frozen source, lines 62–67](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Attainment/PairCompactness.lean#L62-L67).

Hypotheses: Finite matrix index; compact family F; continuous Hermitian V,O; V positive definite on F; admissible p₀∈F with det O(p₀)≠0.

Coverage and boundary: Minimum on nondegenerate locus; inverse-form bound proved on finite cost sublevel. No uniform bound over all squeezing or auxiliary totals.

Module SHA-256: `b2844876d1572a74b032a3309e261c29d78e35007b626773dc082d3134476b70`.


Ambient source variables:

```lean
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]
```


Statement header:

```lean
theorem exists_bosonPairCost_minimum (F : Set X) (hF : IsCompact F)
    (V O : X → HermitianMat ι ℂ) (hV : Continuous V) (hO : Continuous O)
    (hpos : ∀ p ∈ F, (V p).mat.PosDef)
    (p₀ : X) (hp₀ : p₀ ∈ F) (hO₀ : (O p₀).mat.det ≠ 0) :
    ∃ p ∈ F, (O p).mat.det ≠ 0 ∧
      ∀ q ∈ F, (O q).mat.det ≠ 0 → bosonPairCost (V p) (O p) ≤ bosonPairCost (V q) (O q)
```


## B16

`Gaussian.Phase.exists_bosonic_covariance_fixedTotal_minimum`

Paper: Lemma 4.3. [Frozen source, lines 17–23](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMinimum.lean#L17-L23).

Hypotheses: Symmetric V; alternating nondegenerate Ω; uncertainty; nondegenerate physical A; finite M with finrank E≤2M.

Coverage and boundary: Minimum over full raw fixed-total domain and all nondegenerate splits. Existence not asserted for every undersized M.

Module SHA-256: `8d445fea4632143bcdebbc8565ff7ad742d5d9e93cf1705c3078df15f45150de`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
```


Statement header:

```lean
theorem exists_bosonic_covariance_fixedTotal_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate) (M : ℕ)
    (hsize : finrank ℝ E ≤ 2*M) :
    ∃ p : BosonicCovariancePurifier V Ω M,
      ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A
```


## F09

`Gaussian.Physical.Fermion.isCompact_quasifreePurifiers`

Paper: Lemma 4.3 alternate formal route. [Frozen source, lines 62–63](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/StateTopology.lean#L62-L63).

Hypotheses: k,l : ℕ; fixed actual density ρ : Density k.

Coverage and boundary: Compact actual pure-quasifree fixed-marginal domain; may be empty. Formal route uses density compactness, not manuscript Grassmannian orbit proof.

Module SHA-256: `eff89b781ee9a7f802bd1186ea54dcb1a79c2e51c21ce780c140ddb26e8f560f`.


Statement header:

```lean
theorem isCompact_quasifreePurifiers (k l : ℕ) (ρ : Density k) :
    IsCompact {σ : Density (l+k) | IsPureQuasifree σ ∧ prefixRestriction k l σ=ρ}
```


## F10

`Gaussian.Physical.Fermion.exists_sidewise_minimum`

Paper: Lemma 4.3 fixed split. [Frozen source, lines 68–72](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/SidewiseDomain.lean#L68-L72).

Hypotheses: Finite nA,nB,mA,mB; fixed density ρ; explicit nonempty sidewise purifier class.

Coverage and boundary: Attains actual entropy at this split. Nonemptiness is required, not silently inferred for undersized auxiliaries.

Module SHA-256: `fdbac6fdee8776ddfe43507c55dc872133b74d4240b554d0daa45ca35a010be6`.


Statement header:

```lean
theorem exists_sidewise_minimum (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (hne : ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ) :
    ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ ∧
      ∀ τ,IsSidewisePurifier nA nB mA mB ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB mA mB τ
```


## F11

`Gaussian.Physical.Fermion.finitePurifier_attainment`

Paper: Lemma 4.3 all splits. [Frozen source, lines 24–27](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotalDomain.lean#L24-L27).

Hypotheses: Input quasifree ρ; finite M≥nA+nB.

Coverage and boundary: Actual fixed-total minimum including every split; nonemptiness supplied by canonical purification and padding.

Module SHA-256: `c4e7b0d2448a765e000956e280bae6dd4ac5da35cae99a4a90a3e22063d05c8e`.


Statement header:

```lean
theorem finitePurifier_attainment (nA nB : ℕ) (ρ : Density (nA+nB)) (hρ : IsQuasifree ρ)
    (M : ℕ) (hM : nA+nB≤M) :
    ∃ p : FinitePurifier nA nB ρ M,
      ∀ x : FinitePurifier nA nB ρ M,finitePurifierCost nA nB ρ M p≤finitePurifierCost nA nB ρ M x
```


## B17

`Gaussian.Phase.BosonicCovariancePurifier.exists_move_left`

Paper: §5 transfer A′→B′. [Frozen source, lines 46–50](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMoves.lean#L46-L50).

Hypotheses: Raw purifier p at M; Ω alternating; nondegenerate physical A; finrank A<2*p.leftModes.

Coverage and boundary: Same total and marginal, left count decreases one, cost nonincreases. No deletion yet; name left means reducing left count.

Module SHA-256: `2970e439bba7eb29212551c45cf569512cfffe3636bf864211a6add74e70ad96`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}
```


Statement header:

```lean
theorem exists_move_left (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes+1=p.leftModes ∧ q.cost A ≤ p.cost A
```


## B18

`Gaussian.Phase.BosonicCovariancePurifier.exists_move_right`

Paper: §5 transfer B′→A′. [Frozen source, lines 71–76](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainMoves.lean#L71-L76).

Hypotheses: Raw p at M; alternating nondegenerate Ω; nondegenerate A; finrank(Ω.orthogonal A)<2*p.rightModes.

Coverage and boundary: Same total, left count increases one, nonincreasing cost via complementary pure-cut equality.

Module SHA-256: `2970e439bba7eb29212551c45cf569512cfffe3636bf864211a6add74e70ad96`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}
```


Statement header:

```lean
theorem exists_move_right (p : BosonicCovariancePurifier V Ω M)
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ (Ω.orthogonal A) < 2*p.rightModes) :
    ∃ q : BosonicCovariancePurifier V Ω M,
      q.leftModes=p.leftModes+1 ∧ q.cost A ≤ p.cost A
```


## B19

`Gaussian.Phase.BosonicCovariancePurifier.exists_delete_left_at_minimum`

Paper: §5 equality then removal. [Frozen source, lines 17–21](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainDelete.lean#L17-L21).

Hypotheses: Raw p at M+1; Ω alternating; nondegenerate physical A; strict left excess; exact global minimum among all fixed-(M+1) raw purifiers.

Coverage and boundary: Deletes selected globally invariant pure auxiliary plane at exactly equal cost. A minimum only within one split is insufficient.

Module SHA-256: `4b2fcefd4cb42f5eea5a86485175dc66b40eff251f175136467a8eaf2080db97`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}
```


Statement header:

```lean
theorem exists_delete_left_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A = p.cost A
```


## B20

`Gaussian.Phase.BosonicCovariancePurifier.exists_delete_at_minimum`

Paper: §5 either-side removal. [Frozen source, lines 75–80](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainDelete.lean#L75-L80).

Hypotheses: Raw p at M+1; alternating nondegenerate Ω; nondegenerate A; finrank E≤2M; exact fixed-total minimum.

Coverage and boundary: One-step reduction to M with no greater cost; either excessive side. Does not delete from arbitrary nonoptimal states.

Module SHA-256: `4b2fcefd4cb42f5eea5a86485175dc66b40eff251f175136467a8eaf2080db97`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {V Ω : LinearMap.BilinForm ℝ E} {M : ℕ}
```


Statement header:

```lean
theorem exists_delete_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (hΩn : Ω.Nondegenerate)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ E ≤ 2*M)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A ≤ p.cost A
```


## B21

`Gaussian.Phase.BosonicCovariancePurifier.pad_cost`

Paper: §5 padding smaller totals. [Frozen source, lines 133–135](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationAuxPadding.lean#L133-L135).

Hypotheses: Raw p at M; M≤N; physical A with nondegenerate restricted Ω.

Coverage and boundary: Finite pure padding preserves cost exactly; no infinite-dimensional padding theorem.

Module SHA-256: `4126ad042a9fd96537a2e82b201c3dd6174ec5f7627d95c23868697eb74b7cc6`.


Ambient source variables:

```lean
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}
variable {Ω : LinearMap.BilinForm ℝ E} {σ : LinearMap.BilinForm ℝ F}
  {τ : LinearMap.BilinForm ℝ G}
variable {H : Type u} [AddCommGroup H] [Module ℝ H] [FiniteDimensional ℝ H]
  {V Ω : LinearMap.BilinForm ℝ H} {M N : ℕ}
```


Statement header:

```lean
theorem pad_cost (p : BosonicCovariancePurifier V Ω M) (hMN : M≤N)
    (A : Submodule ℝ H) (hA : (Ω.restrict A).Nondegenerate) :
    (p.pad hMN).cost A = p.cost A
```


## F12

`Gaussian.Physical.Fermion.exists_A_excess_transfer`

Paper: §5 transfer and equality. [Frozen source, lines 14–20](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AExcessTransfer.lean#L14-L20).

Hypotheses: nA<a+1; actual input ρ; actual sidewise purifier σ at (a+1,b).

Coverage and boundary: Actual purifier at (a,b+1) with nonincrease; exact equality gives pure transferred terminal mode. Both components allowed.

Module SHA-256: `292cfb1958ecea1b4546f9a0d5d2719322e30e09d2bb3087a42ec894b4b07869`.


Statement header:

```lean
theorem exists_A_excess_transfer (nA nB a b : ℕ) (hexcess : nA<a+1)
    (ρ : Density (nA+nB)) (σ : Density (((a+1)+b)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB (a+1) b ρ σ) :
    ∃ τ : Density ((a+(b+1))+(nA+nB)),IsSidewisePurifier nA nB a (b+1) ρ τ ∧
      sidewiseEntropy nA nB a (b+1) τ≤sidewiseEntropy nA nB (a+1) b σ ∧
      (sidewiseEntropy nA nB a (b+1) τ=sidewiseEntropy nA nB (a+1) b σ →
        ∃ ψ,suffixRestriction ((a+b)+(nA+nB)) 1 (modeCountCast (by omega) τ)=MState.pure ψ)
```


## F13

`Gaussian.Physical.Fermion.exists_B_excess_transfer`

Paper: §5 opposite transfer. [Frozen source, lines 11–16](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/BExcessTransfer.lean#L11-L16).

Hypotheses: nB<b+1; actual sidewise purifier σ at (a,b+1).

Coverage and boundary: Actual purifier at (a+1,b) with nonincrease; derived via signed party swap and complementary entropy. Public statement has no separate equality callback.

Module SHA-256: `58a29d85d7baf63a3b8ea30e509d8c72277c385a0e9f1ae2f37a6f301e32f752`.


Statement header:

```lean
theorem exists_B_excess_transfer (nA nB a b : ℕ) (hexcess : nB<b+1)
    (ρ : Density (nA+nB)) (σ : Density ((a+(b+1))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB a (b+1) ρ σ) :
    ∃ τ : Density (((a+1)+b)+(nA+nB)),
      IsSidewisePurifier nA nB (a+1) b ρ τ ∧
      sidewiseEntropy nA nB (a+1) b τ≤sidewiseEntropy nA nB a (b+1) σ
```


## F14

`Gaussian.Physical.Fermion.exists_sidewise_pure_B_entropy_deletion`

Paper: §5 / Appendix B deletion. [Frozen source, lines 69–75](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/PureDeletion.lean#L69-L75).

Hypotheses: Actual sidewise purifier at (mA,mB+extra); extra-mode suffix covariance pure after exact mode-count cast.

Coverage and boundary: Smaller actual pure-quasifree purifier, fixed physical density and exactly preserved cut entropy. Full signature gives terminal ordering.

Module SHA-256: `d2c5afb56840e85398a0b4119f093a559f3a70623dfa62f2e6abc3cfb874c2d8`.


Statement header:

```lean
theorem exists_sidewise_pure_B_entropy_deletion (nA nB mA mB extra : ℕ) (ρ : Density (nA+nB))
    (σ : Density ((mA+(mB+extra))+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA (mB+extra) ρ σ)
    (hs : CovariancePure (suffixRestriction ((mA+mB)+(nA+nB)) extra
      (modeCountCast (by omega) σ))) :
    ∃ τ : Density ((mA+mB)+(nA+nB)),IsSidewisePurifier nA nB mA mB ρ τ ∧
      sidewiseEntropy nA nB mA mB τ=sidewiseEntropy nA nB mA (mB+extra) σ
```


## F15

`Gaussian.Physical.Fermion.finitePurifier_optimal_delete`

Paper: §5 optimal deletion. [Frozen source, lines 41–46](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/OptimalDeletion.lean#L41-L46).

Hypotheses: M≥nA+nB; actual FinitePurifier at M+1; exact minimum over all FinitePurifier at that total.

Coverage and boundary: Smaller feasible point with cost ≤ old minimum; equality follows using pure padding, not asserted by this interface alone.

Module SHA-256: `bf89d358b9c1191554669cb42f525f61bbca8a10d2afd3cea756e815e1408dce`.


Statement header:

```lean
theorem finitePurifier_optimal_delete (nA nB : ℕ) (ρ : Density (nA+nB)) (M : ℕ)
    (hM : nA+nB≤M) (p : FinitePurifier nA nB ρ (M+1))
    (hp : ∀ x : FinitePurifier nA nB ρ (M+1),
      finitePurifierCost nA nB ρ (M+1) p≤finitePurifierCost nA nB ρ (M+1) x) :
    ∃ q : FinitePurifier nA nB ρ M,
      finitePurifierCost nA nB ρ M q≤finitePurifierCost nA nB ρ (M+1) p
```


## F16

`Gaussian.Physical.Fermion.finitePurifier_padding`

Paper: §5 padding. [Frozen source, lines 34–37](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/FiniteTotalPadding.lean#L34-L37).

Hypotheses: M≤L; actual FinitePurifier at M.

Coverage and boundary: Actual point at L with exactly unchanged cost; finite only.

Module SHA-256: `023fe89f8f1cd9bf8048ddb9a0ac93de2573834953606e181a52967d806977f5`.


Statement header:

```lean
theorem finitePurifier_padding (nA nB : ℕ) (ρ : Density (nA+nB)) (M L : ℕ) (hML : M≤L)
    (p : FinitePurifier nA nB ρ M) :
    ∃ q : FinitePurifier nA nB ρ L,
      finitePurifierCost nA nB ρ L q=finitePurifierCost nA nB ρ M p
```


## G01

`Gaussian.Optimization.global_attained_from_optimal_deletion`

Paper: §5 all-finite induction. [Frozen source, lines 13–20](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Optimization/FiniteDescent.lean#L13-L20).

Hypotheses: Dependent domains E M and real cost; attainment for M≥n; deletion at exact minima; padding for M<n.

Coverage and boundary: Generic logical theorem. All three premises must be proved in each physical sector; alone it is not a Gaussian theorem.

Module SHA-256: `d678f0a0ac4eb4ba227596c2096cdbde4d792ca55626c1bbcd240433fa8a61f7`.


Statement header:

```lean
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

Paper: §5 matched split. [Frozen source, lines 10–14](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Optimization/MatchedIteration.lean#L10-L14).

Hypotheses: Natural-number index and real cost; up/down unit moves toward target with cost nonincrease; initial point x.

Coverage and boundary: Finite termination at exact target. No optimizer uniqueness or infinite limit.

Module SHA-256: `e9e725b9f0285cd5cdaf051106415bbd1ab7d9a9c746ee60f33173e571c0476b`.


Statement header:

```lean
theorem exists_matched_cost_le_of_unit_moves {E : Type*} (index : E → ℕ)
    (cost : E → ℝ) (target : ℕ)
    (up : ∀ x,index x<target → ∃ y,index y=index x+1 ∧ cost y≤cost x)
    (down : ∀ x,target < index x → ∃ y,index y+1=index x ∧ cost y≤cost x)
    (x : E) : ∃ y,index y=target ∧ cost y≤cost x
```


## B22

`Gaussian.Phase.exists_bosonic_covariance_allFinite_matched_minimum`

Paper: Theorem 2.1 covariance core. [Frozen source, lines 21–28](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationMinimum.lean#L21-L28).

Hypotheses: Symmetric uncertainty-admissible V; alternating nondegenerate Ω; nondegenerate A; dim E=2(nA+nB), dim A=2nA.

Coverage and boundary: Matched raw witness compared with every finite raw auxiliary total/carrier/split. Actual states follow B06/B07.

Module SHA-256: `feaa2f0b725b7b5c23b3428fc8e82e1f8cd96c80f2ed7d9b1e698ad60226dd78`.


Ambient source variables:

```lean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
```


Statement header:

```lean
theorem exists_bosonic_covariance_allFinite_matched_minimum
    (V Ω : LinearMap.BilinForm ℝ E) (hV : V.IsSymm) (hΩa : Ω.IsAlt)
    (hΩn : Ω.Nondegenerate) (hUnc : Gaussian.Covariance.RealifiedUncertainty V Ω)
    (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (nA nB : ℕ) (hd : finrank ℝ E=2*(nA+nB)) (hAd : finrank ℝ A=2*nA) :
    ∃ p : BosonicCovariancePurifier V Ω (nA+nB),
      p.leftModes=nA ∧ p.rightModes=nB ∧
      ∀ M : ℕ, ∀ q : BosonicCovariancePurifier V Ω M, p.cost A ≤ q.cost A
```


## F17

`Gaussian.Physical.Fermion.finitePurifier_matchSplit`

Paper: §5 matched split. [Frozen source, lines 18–22](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/MatchedSplit.lean#L18-L22).

Hypotheses: Actual FinitePurifier at total nA+nB.

Coverage and boundary: Actual matched witness with no greater cost; applied to globally optimal point gives optimizer.

Module SHA-256: `9f0c2c0d50ea2d92150c15dd889b53b7b80cacddb9c9ad28f99a3cb63dd60b41`.


Statement header:

```lean
theorem finitePurifier_matchSplit (nA nB : ℕ) (ρ : Density (nA+nB))
    (p : FinitePurifier nA nB ρ (nA+nB)) :
    ∃ σ : Density ((nA+nB)+(nA+nB)),
      IsSidewisePurifier nA nB nA nB ρ σ ∧
      sidewiseEntropy nA nB nA nB σ≤finitePurifierCost nA nB ρ (nA+nB) p
```


## B23

`Gaussian.Physical.Boson.infimum_eq_of_global_sidewise_witness`

Paper: Theorem 2.1 infimum identification. [Frozen source, lines 24–29](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/AllFiniteDomain.lean#L24-L29).

Hypotheses: Actual feasible σ at finite pair; comparison with every actual finite sidewise purifier.

Coverage and boundary: Identifies ENNReal infimum with witness entropy. Finiteness is separately provided by B01/B03.

Module SHA-256: `67cc1aa615bbc0817aab58c3be72d8c73e5fa14241cee2dd0ed61ee932955b24`.


Statement header:

```lean
theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : BipartiteDensity nA nB) (σ : FourPartyDensity nA nB mA mB)
    (hσ : IsSidewisePurifier ρ σ)
    (hmin : ∀ a b : ℕ,∀ τ : FourPartyDensity nA nB a b,
      IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy σ
```


## F18

`Gaussian.Physical.Fermion.infimum_eq_of_global_sidewise_witness`

Paper: Theorem 2.1 infimum identification. [Frozen source, lines 56–62](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean#L56-L62).

Hypotheses: Actual feasible σ at finite pair; universal finite-pair comparison.

Coverage and boundary: Identifies real sInf using nonempty class and entropy lower bound. No non-Gaussian competitor.

Module SHA-256: `7927a3e38f056af8881d06b97546e3c63dd269021fd695d68f37b5862ce4c89c`.


Statement header:

```lean
theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ)
    (hmin : ∀ (a b : ℕ) (τ : Density ((a+b)+(nA+nB))),
      IsSidewisePurifier nA nB a b ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB a b τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy nA nB mA mB σ
```


## F19

`Gaussian.Physical.Fermion.allFiniteCosts_iff_finitePurifier`

Paper: Theorem 2.1 domain completeness. [Frozen source, lines 43–45](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean#L43-L45).

Hypotheses: Finite nA,nB; actual physical density ρ; real c.

Coverage and boundary: Actual all-pair feasible costs iff a finite-total purifier has cost c. No finite-total truncation.

Module SHA-256: `7927a3e38f056af8881d06b97546e3c63dd269021fd695d68f37b5862ce4c89c`.


Statement header:

```lean
theorem allFiniteCosts_iff_finitePurifier (nA nB : ℕ) (ρ : Density (nA+nB)) (c : ℝ) :
    c ∈ allFinitePurificationCosts nA nB ρ ↔
      ∃ (M : ℕ) (p : FinitePurifier nA nB ρ M),finitePurifierCost nA nB ρ M p=c
```


## B24

`Gaussian.Physical.Boson.IsGaussianWith.eq_product_of_cross_zero`

Paper: Lemma 3.1 factor semantics. [Frozen source, lines 50–56](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/GaussianFactorization.lean#L50-L56).

Hypotheses: Finite configuration E,F; actual Gaussian density with mean m and covariance V; all cross covariance entries zero.

Coverage and boundary: Actual density is product of actual left and right reductions. Gaussianity and full cross-block hypothesis required.

Module SHA-256: `2efbeddad68e05a32b5950cd89a291289f3f24ec67bcc40d19ef98183fe40876`.


Ambient source variables:

```lean
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
```


Statement header:

```lean
theorem IsGaussianWith.eq_product_of_cross_zero
    {ρ : NormalDensity (Schrodinger (JointConfiguration E F))}
    {m : (JointConfiguration E F×JointConfiguration E F) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (JointConfiguration E F×JointConfiguration E F)}
    (hρ : IsGaussianWith ρ m V)
    (hcross : ∀ z : E×E,∀ w : F×F,V (leftPhaseEmbedding z) (rightPhaseEmbedding w)=0) :
    ρ=ρ.leftReduction.product ρ.rightReduction
```


## B25

`Gaussian.Physical.Boson.NormalDensity.entropy_eq_of_traceClass`

Paper: §2 actual entropy semantics. [Frozen source, lines 52–54](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/NormalEntropy.lean#L52-L54).

Hypotheses: Complete complex Hilbert space; positive normalized trace-class NormalDensity; entropyOperator trace class.

Coverage and boundary: Extended entropy equals real trace of CFC −ρ log ρ. General normal-density bridge; Gaussian finiteness is proved separately.

Module SHA-256: `52cfe0853c97b77500651f0ac4bf34c97131903bb455dc91a625a0fdb15bb37d`.


Ambient source variables:

```lean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
```


Statement header:

```lean
theorem NormalDensity.entropy_eq_of_traceClass (ρ : NormalDensity H)
    (h : IsTraceClass ρ.entropyOperator) :
    ρ.entropy = ENNReal.ofReal (trace ρ.entropyOperator h).re
```
