import Gaussian.Physical.Boson.NormalFormCoordinates
import Gaussian.Physical.Boson.SymplecticImplementation
import Gaussian.Physical.Boson.GaussianClassification
import Gaussian.Phase.BosonicPurificationReindex

/-! Actual finite-mode normal Gaussian realization and entropy classification from raw
uncertainty. All conjugations act on the full Schrödinger Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open Module Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A raw paired basis is realized by an actual unitarily transformed thermal operator. -/
theorem exists_gaussian_of_mode_basis {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n × Bool) ℝ (E×E)) (V : LinearMap.BilinForm ℝ (E×E))
    (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (hbV : ∀ i j, V (b i) (b j)=if i=j then ν i.1 else 0)
    (hbΩ : ∀ i j, weylSymplecticForm E (b i) (b j)=
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
        else (if j.2 then 1 else 0)) else 0) :
    ∃ ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ 0 V ∧
      ρ.entropy=ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) ∧
      ((∀ i, ν i=1) → ρ.IsPure) := by
  obtain ⟨U,hU⟩ := exists_weyl_implementation (normalFormEquiv a b)
    (normalFormEquiv_symplectic a b hbΩ)
  refine ⟨(canonicalThermalOn a.repr ν hν).conjugate U,?_,?_,?_⟩
  · have hg := hU.gaussian (canonicalThermalOn_isGaussian a.repr ν hν)
    simpa only [LinearMap.zero_comp,normalFormEquiv_covariance a b V ν hbV] using hg
  · rw [NormalDensity.entropy_conjugate,canonicalThermalOn_entropy]
  · intro hp
    exact ((canonicalThermalOn_isPure_iff a.repr ν hν).mpr hp).conjugate U

/-- Every symmetric covariance satisfying the true Weyl uncertainty condition, with
arbitrary finite linear mean, is realized by a positive trace-class trace-one density.
Its actual extended CFC entropy is the independent Hermitian covariance-form cost. -/
theorem exists_gaussian_with_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) (V : LinearMap.BilinForm ℝ (E×E)) (hV : V.IsSymm)
    (hunc : Gaussian.Covariance.RealifiedUncertainty V (weylSymplecticForm E))
    (m : (E×E) →ₗ[ℝ] ℝ) :
    ∃ ρ : NormalDensity (Schrodinger E), IsGaussianWith ρ m V ∧
      ρ.entropy=ENNReal.ofReal (bosonFormCost e V (weylSymplecticForm E) hV weylSymplecticForm_isAlt) := by
  obtain ⟨ν,b,hν,hbV,hbΩ⟩ := exists_williamson_phase_basis V hV hunc
  obtain ⟨ρ,hg,he,hp⟩ := exists_gaussian_of_mode_basis (stdOrthonormalBasis ℝ E) b V ν hν hbV hbΩ
  obtain ⟨a,c,hm,hem⟩ := hg.exists_prescribed_mean m
  refine ⟨ρ.displace a c,hm,?_⟩
  rw [hem,he,bosonFormCost_eq_sum_of_mode_basis e b V (weylSymplecticForm E)
    hV weylSymplecticForm_isAlt ν hν hbV hbΩ]

/-- Actual entropy of every raw finite-mode normal Gaussian equals the independent
covariance objective. The extended entropy is proved finite as a consequence. -/
theorem IsGaussianWith.entropy_eq_bosonFormCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ (E×E)) {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) :
    ρ.entropy=ENNReal.ofReal (bosonFormCost e V (weylSymplecticForm E) hρ.1 weylSymplecticForm_isAlt) := by
  obtain ⟨σ,hσ,he⟩ := exists_gaussian_with_entropy e V hρ.1 hρ.uncertainty m
  exact (congrArg NormalDensity.entropy (hρ.density_unique hσ)).trans he

theorem IsGaussianWith.entropy_ne_top {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) : ρ.entropy≠⊤ := by
  rw [hρ.entropy_eq_bosonFormCost (phaseBasis (stdOrthonormalBasis ℝ E).toBasis)]
  exact ENNReal.ofReal_ne_top

/-- Within the actual Gaussian class, zero CFC entropy is equivalent to true rank-one purity. -/
theorem IsGaussianWith.isPure_iff_entropy_eq_zero {ρ : NormalDensity (Schrodinger E)}
    {m : (E×E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E×E)}
    (hρ : IsGaussianWith ρ m V) : ρ.IsPure ↔ ρ.entropy=0 := by
  classical
  refine ⟨NormalDensity.IsPure.entropy_eq_zero,?_⟩
  intro he0
  obtain ⟨ν,b,hν,hbV,hbΩ⟩ := exists_williamson_phase_basis V hρ.1 hρ.uncertainty
  obtain ⟨σ,hσ,he,hp⟩ := exists_gaussian_of_mode_basis (stdOrthonormalBasis ℝ E) b V ν hν hbV hbΩ
  obtain ⟨a,c,hm,hem⟩ := hσ.exists_prescribed_mean m
  have hρeq := hρ.density_unique hm
  have hs : ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i))=0 := by
    rw [← he,← hem,← hρeq,he0]
  have hsum : ∑ i, Gaussian.Entropy.boson (ν i)=0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hs)
      (Finset.sum_nonneg (fun i hi => Gaussian.Entropy.boson_nonneg (hν i)))
  have hνone : ∀ i, ν i=1 := by
    intro i
    apply (Gaussian.Entropy.boson_eq_zero_iff (hν i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => Gaussian.Entropy.boson_nonneg (hν j))).mp hsum i (Finset.mem_univ i)
  rw [hρeq]
  exact (hp hνone).displace a c

end Gaussian.Physical.Boson
