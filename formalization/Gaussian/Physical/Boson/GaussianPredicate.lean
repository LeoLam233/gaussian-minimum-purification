import Gaussian.Physical.Boson.Characteristic

/-! Raw bosonic Gaussianity stated through the actual Schrödinger Weyl characteristic.
Symmetry is explicit, so antisymmetric changes of V are not silently accepted.
The predicate imposes no realization, entropy, purity or reduction conclusions as fields. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Mean and covariance in the Weyl coefficient convention W(q,p)f(x)=e^{ip(x+q/2)}f(x+q).
For physical position/momentum means (dQ,dP), m(q,p)=p·dQ+q·dP. -/
def IsGaussianWith (ρ : NormalDensity (Schrodinger E))
    (m : (E × E) →ₗ[ℝ] ℝ) (V : LinearMap.BilinForm ℝ (E × E)) : Prop :=
  V.IsSymm ∧ ∀ q p, ρ.characteristic q p =
    Complex.exp ((m (q,p) : ℂ)*Complex.I - (V (q,p) (q,p) : ℂ)/4)

def displacementMean (a b : E) : (E × E) →ₗ[ℝ] ℝ where
  toFun z := ⟪b,z.1⟫_ℝ - ⟪z.2,a⟫_ℝ
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]; ring
  map_smul' r z := by
    change ⟪b,r • z.1⟫_ℝ - ⟪r • z.2,a⟫_ℝ = r * (⟪b,z.1⟫_ℝ - ⟪z.2,a⟫_ℝ)
    simp only [inner_smul_left, inner_smul_right, conj_trivial]
    ring

theorem IsGaussianWith.displace {ρ : NormalDensity (Schrodinger E)}
    {m : (E × E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E × E)}
    (h : IsGaussianWith ρ m V) (a b : E) :
    IsGaussianWith (ρ.displace a b) (m + displacementMean a b) V := by
  refine ⟨h.1,?_⟩
  intro q p
  rw [NormalDensity.characteristic_displace, h.2 q p, ← Complex.exp_add]
  congr 1
  simp only [LinearMap.add_apply, displacementMean, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.ofReal_add]
  ring

/-- Every finite displacement keeps the covariance characteristic term and actual entropy. -/
theorem IsGaussianWith.displace_entropy {ρ : NormalDensity (Schrodinger E)}
    {m : (E × E) →ₗ[ℝ] ℝ} {V : LinearMap.BilinForm ℝ (E × E)}
    (h : IsGaussianWith ρ m V) (a b : E) :
    IsGaussianWith (ρ.displace a b) (m + displacementMean a b) V ∧
      (ρ.displace a b).entropy = ρ.entropy := ⟨h.displace a b, ρ.entropy_displace a b⟩

end Gaussian.Physical.Boson
