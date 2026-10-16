# Supplementary declaration crosswalk: non-overlapping PR #1 entries

These eleven declarations were present in the 13 October 2026 verification appendix draft ([PR #1](https://github.com/LeoLam233/gaussian-minimum-purification/pull/1)) but absent from the mainline 62-entry selective declaration register at the time of integration. This is **supplementary navigation**, not a replacement for the main appendix, a new Lean proof, or an extension of the v0.1.3 frozen formalization.

The statements and full-file source SHA-256 values below are transcribed from the PR's pinned `declarations.json`; the source references target Lean v0.1.3 commit `62820a0afff79559be7c3af99cc23a8c7550ac5c`. The main appendix and its 62 stable IDs are unchanged. Some similarly named theorems are related but not definitionally identical, hence the selection is by exact qualified declaration name and path.

## 1. `Gaussian.Physical.Boson.IsGaussianWith.sidewiseReduction`

Paper locus: §2 actual subsystem semantics.

Scope: True AA′ reduction has restricted mean and covariance; complete subsystem, not arbitrary coefficient deletion.

Hypotheses: Finite configurations A,B,C,D; actual four-party IsGaussianWith σ m V.

Frozen source: [formalization/Gaussian/Physical/Boson/SidewiseDomain.lean lines 51–57](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/SidewiseDomain.lean#L51-L57)

Source SHA-256: `34ecd522db762c9c93859845be00489ccd1f5b4e33a9d9cdd73c135ff0923b6b`

```lean
theorem IsGaussianWith.sidewiseReduction
    {σ : NormalDensity (Schrodinger (FourConfiguration A B C D))}
    {m : (FourConfiguration A B C D×FourConfiguration A B C D) →ₗ[ℝ] ℝ}
    {V : LinearMap.BilinForm ℝ (FourConfiguration A B C D×FourConfiguration A B C D)}
    (hσ : IsGaussianWith σ m V) :
    IsGaussianWith (sidewiseReduction σ) (m.comp sidewisePhaseEmbedding)
      (V.compl₁₂ sidewisePhaseEmbedding sidewisePhaseEmbedding)
```

## 2. `Gaussian.Phase.exists_bosonic_product_selection`

Paper locus: Lemma 3.1, §3.2.

Scope: Selected auxiliary plane, symplectic complement, nonincrease, equality implies pure plane covariance. Covariance statement, not standalone physical factorization iff.

Hypotheses: Finite real modules E,F; symmetric V on E×F; alternating nondegenerate Ω,σ; product uncertainty; finrank E < finrank F.

Frozen source: [formalization/Gaussian/Phase/BosonicPurificationProductSelection.lean lines 31–47](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationProductSelection.lean#L31-L47)

Source SHA-256: `bf2f45fb18e290b6a5d0da643c54e4a79d9f3abae821e4497bec4525111c4db3`

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

## 3. `Gaussian.Phase.BosonicAdaptationData.restricted_formCost_le`

Paper locus: Lemma 3.1 inequality.

Scope: Covariance cost comparison. Actual entropy needs B03 and subsystem bridges.

Hypotheses: Finite real module; adaptation d; alternating Ω; g≤V; J-invariant U; full and retained Boolean mode bases.

Frozen source: [formalization/Gaussian/Phase/BosonicPurificationRigidity.lean lines 27–31](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L27-L31)

Source SHA-256: `8d6ddfb4feaeb534c577eaf2e74856a7b5ed4ea1cdd33fad631e6f03ce0b0af0`

```lean
theorem restricted_formCost_le (hΩ : Ω.IsAlt) (hLower : ∀ x, d.g x x ≤ V x x)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, d.J x ∈ U) {n m : ℕ}
    (e : Basis (Fin n × Bool) ℝ E) (eU : Basis (Fin m × Bool) ℝ U) :
    bosonFormCost eU (V.restrict U) (Ω.restrict U) (d.covariance_symmetric.restrict U)
        (fun x => hΩ x) ≤ bosonFormCost e V Ω d.covariance_symmetric hΩ
```

## 4. `Gaussian.Phase.BosonicAdaptationData.exists_pure_discarded_of_formCost_eq`

Paper locus: Lemma 3.1 pure endpoint.

Scope: Constructs PureCompatibleCovariance on the discarded complement; physical realization is separate.

Hypotheses: B10 hypotheses plus exact cost equality.

Frozen source: [formalization/Gaussian/Phase/BosonicPurificationRigidity.lean lines 103–110](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationRigidity.lean#L103-L110)

Source SHA-256: `8d6ddfb4feaeb534c577eaf2e74856a7b5ed4ea1cdd33fad631e6f03ce0b0af0`

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

## 5. `Gaussian.Physical.Fermion.quasifree_entropy_eq_hermitianCost`

Paper locus: §2 entropy formula.

Scope: Actual von Neumann entropy equals covariance Hermitian cost; includes zero/repeated/pure endpoints.

Hypotheses: n : ℕ; ρ : Density n; IsQuasifree ρ.

Frozen source: [formalization/Gaussian/Physical/Fermion/OrthogonalSpectrum.lean lines 92–93](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/OrthogonalSpectrum.lean#L92-L93)

Source SHA-256: `e8c92709fbcc790be0a490f3d7bd786ea9e48071c47bd5f2e1392f0ea3da087d`

```lean
theorem quasifree_entropy_eq_hermitianCost (n : ℕ) (ρ : Density n) (hρ : IsQuasifree ρ) :
    Sᵥₙ ρ = Gaussian.Attainment.fermionHermitianCost (covarianceHermitianMat ρ)
```

## 6. `Gaussian.Physical.Fermion.exists_sidewise_minimum`

Paper locus: Lemma 4.3 fixed split.

Scope: Attains actual entropy at this split. Nonemptiness is required, not silently inferred for undersized auxiliaries.

Hypotheses: Finite nA,nB,mA,mB; fixed density ρ; explicit nonempty sidewise purifier class.

Frozen source: [formalization/Gaussian/Physical/Fermion/SidewiseDomain.lean lines 68–72](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/SidewiseDomain.lean#L68-L72)

Source SHA-256: `fdbac6fdee8776ddfe43507c55dc872133b74d4240b554d0daa45ca35a010be6`

```lean
theorem exists_sidewise_minimum (nA nB mA mB : ℕ) (ρ : Density (nA+nB))
    (hne : ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ) :
    ∃ σ,IsSidewisePurifier nA nB mA mB ρ σ ∧
      ∀ τ,IsSidewisePurifier nA nB mA mB ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB mA mB τ
```

## 7. `Gaussian.Phase.BosonicCovariancePurifier.exists_delete_left_at_minimum`

Paper locus: §5 equality then removal.

Scope: Deletes selected globally invariant pure auxiliary plane at exactly equal cost. A minimum only within one split is insufficient.

Hypotheses: Raw p at M+1; Ω alternating; nondegenerate physical A; strict left excess; exact global minimum among all fixed-(M+1) raw purifiers.

Frozen source: [formalization/Gaussian/Phase/BosonicPurificationDomainDelete.lean lines 17–21](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Phase/BosonicPurificationDomainDelete.lean#L17-L21)

Source SHA-256: `4b2fcefd4cb42f5eea5a86485175dc66b40eff251f175136467a8eaf2080db97`

```lean
theorem exists_delete_left_at_minimum (p : BosonicCovariancePurifier V Ω (M+1))
    (hΩa : Ω.IsAlt) (A : Submodule ℝ E) (hA : (Ω.restrict A).Nondegenerate)
    (hExcess : finrank ℝ A < 2*p.leftModes)
    (hmin : ∀ q : BosonicCovariancePurifier V Ω (M+1), p.cost A ≤ q.cost A) :
    ∃ q : BosonicCovariancePurifier V Ω M, q.cost A = p.cost A
```

## 8. `Gaussian.Physical.Boson.infimum_eq_of_global_sidewise_witness`

Paper locus: Theorem 2.1 infimum identification.

Scope: Identifies ENNReal infimum with witness entropy. Finiteness is separately provided by B01/B03.

Hypotheses: Actual feasible σ at finite pair; comparison with every actual finite sidewise purifier.

Frozen source: [formalization/Gaussian/Physical/Boson/AllFiniteDomain.lean lines 24–29](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/AllFiniteDomain.lean#L24-L29)

Source SHA-256: `67cc1aa615bbc0817aab58c3be72d8c73e5fa14241cee2dd0ed61ee932955b24`

```lean
theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : BipartiteDensity nA nB) (σ : FourPartyDensity nA nB mA mB)
    (hσ : IsSidewisePurifier ρ σ)
    (hmin : ∀ a b : ℕ,∀ τ : FourPartyDensity nA nB a b,
      IsSidewisePurifier ρ τ → sidewiseEntropy σ≤sidewiseEntropy τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy σ
```

## 9. `Gaussian.Physical.Fermion.infimum_eq_of_global_sidewise_witness`

Paper locus: Theorem 2.1 infimum identification.

Scope: Identifies real sInf using nonempty class and entropy lower bound. No non-Gaussian competitor.

Hypotheses: Actual feasible σ at finite pair; universal finite-pair comparison.

Frozen source: [formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean lines 56–62](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean#L56-L62)

Source SHA-256: `7927a3e38f056af8881d06b97546e3c63dd269021fd695d68f37b5862ce4c89c`

```lean
theorem infimum_eq_of_global_sidewise_witness (nA nB mA mB : ℕ)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ)
    (hmin : ∀ (a b : ℕ) (τ : Density ((a+b)+(nA+nB))),
      IsSidewisePurifier nA nB a b ρ τ →
        sidewiseEntropy nA nB mA mB σ≤sidewiseEntropy nA nB a b τ) :
    gaussianPurificationInfimum nA nB ρ=sidewiseEntropy nA nB mA mB σ
```

## 10. `Gaussian.Physical.Fermion.allFiniteCosts_iff_finitePurifier`

Paper locus: Theorem 2.1 domain completeness.

Scope: Actual all-pair feasible costs iff a finite-total purifier has cost c. No finite-total truncation.

Hypotheses: Finite nA,nB; actual physical density ρ; real c.

Frozen source: [formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean lines 43–45](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Fermion/AllFiniteDomain.lean#L43-L45)

Source SHA-256: `7927a3e38f056af8881d06b97546e3c63dd269021fd695d68f37b5862ce4c89c`

```lean
theorem allFiniteCosts_iff_finitePurifier (nA nB : ℕ) (ρ : Density (nA+nB)) (c : ℝ) :
    c ∈ allFinitePurificationCosts nA nB ρ ↔
      ∃ (M : ℕ) (p : FinitePurifier nA nB ρ M),finitePurifierCost nA nB ρ M p=c
```

## 11. `Gaussian.Physical.Boson.NormalDensity.entropy_eq_of_traceClass`

Paper locus: §2 actual entropy semantics.

Scope: Extended entropy equals real trace of CFC −ρ log ρ. General normal-density bridge; Gaussian finiteness is proved separately.

Hypotheses: Complete complex Hilbert space; positive normalized trace-class NormalDensity; entropyOperator trace class.

Frozen source: [formalization/Gaussian/Physical/Boson/NormalEntropy.lean lines 52–54](https://github.com/LeoLam233/gaussian-minimum-purification/blob/62820a0afff79559be7c3af99cc23a8c7550ac5c/formalization/Gaussian/Physical/Boson/NormalEntropy.lean#L52-L54)

Source SHA-256: `52cfe0853c97b77500651f0ac4bf34c97131903bb455dc91a625a0fdb15bb37d`

```lean
theorem NormalDensity.entropy_eq_of_traceClass (ρ : NormalDensity H)
    (h : IsTraceClass ρ.entropyOperator) :
    ρ.entropy = ENNReal.ofReal (trace ρ.entropyOperator h).re
```

This supplemental document reflects the PR's source-excerpt inventory; formal theorem checking remains governed by the existing build and validation evidence.
