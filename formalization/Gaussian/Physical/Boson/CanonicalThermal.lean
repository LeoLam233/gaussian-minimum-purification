import Gaussian.Physical.Boson.CanonicalBasis
import Gaussian.Physical.Boson.CanonicalCovariance
import Gaussian.Physical.Boson.ThermalProductDensity
import Gaussian.Physical.Boson.NormalMixtureObservation

/-! Actual finite-mode canonical thermal states and their Weyl characteristic factorization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
open scoped InnerProductSpace

def canonicalThermalDensity {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    NormalDensity (Schrodinger (CanonicalConfiguration n)) :=
  thermalProductDensity (canonicalOscillatorBasis n) ν hν

theorem canonicalThermalDensity_entropy {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (canonicalThermalDensity ν hν).entropy=ENNReal.ofReal (∑ i, Gaussian.Entropy.boson (ν i)) :=
  thermalProductDensity_entropy (canonicalOscillatorBasis n) ν hν

theorem canonicalThermalDensity_isPure_iff {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ i, 1 ≤ ν i) :
    (canonicalThermalDensity ν hν).IsPure ↔ ∀ i, ν i=1 :=
  thermalProductDensity_isPure_iff (canonicalOscillatorBasis n) ν hν

lemma occupationThermalWeight_cons {n : ℕ} (ν : Fin (n+1) → ℝ) (j : ℕ) (k : Fin n → ℕ) :
    occupationThermalWeight ν (Fin.cons j k)=
      thermalWeight (thermalRatio (ν 0)) j * occupationThermalWeight (fun i : Fin n => ν i.succ) k := by
  simp only [occupationThermalWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem canonicalThermalDensity_characteristic_hasSum {n : ℕ} (ν : Fin n → ℝ)
    (hν : ∀ i, 1 ≤ ν i) (q p : CanonicalConfiguration n) :
    HasSum (fun k : Fin n → ℕ => (occupationThermalWeight ν k : ℂ)*
      ⟪canonicalOscillatorBasis n k,weyl q p (canonicalOscillatorBasis n k)⟫_ℂ)
      ((canonicalThermalDensity ν hν).characteristic q p) :=
  hasSum_normalMixture_expect _ (occupationThermalWeight_nonneg ν hν)
    (hasSum_occupationThermalWeight ν hν) (canonicalOscillatorBasis n)
    (canonicalOscillatorBasis n).orthonormal.norm_eq_one (weylOperator q p)

/-- Exact one-mode/tail factorization of the actual trace characteristic. -/
theorem canonicalThermalDensity_characteristic_succ {n : ℕ} (ν : Fin (n+1) → ℝ)
    (hν : ∀ i, 1 ≤ ν i) (q p : CanonicalConfiguration (n+1)) :
    (canonicalThermalDensity ν hν).characteristic q p =
      (schrodingerThermalDensity unitOscillator (thermalRatio (ν 0)) (thermalRatio_mem (hν 0))).characteristic (q 0) (p 0) *
      (canonicalThermalDensity (fun i : Fin n => ν i.succ) (fun i => hν i.succ)).characteristic
        (toLp 2 (fun i : Fin n => q i.succ)) (toLp 2 (fun i : Fin n => p i.succ)) := by
  let a : ℕ → ℂ := fun j => (thermalWeight (thermalRatio (ν 0)) j : ℂ)*
    ⟪unitOscillatorBasis j,weyl (q 0) (p 0) (unitOscillatorBasis j)⟫_ℂ
  let b : (Fin n → ℕ) → ℂ := fun k => (occupationThermalWeight (fun i : Fin n => ν i.succ) k : ℂ)*
    ⟪canonicalOscillatorBasis n k,
      weyl (toLp 2 (fun i : Fin n => q i.succ)) (toLp 2 (fun i : Fin n => p i.succ))
        (canonicalOscillatorBasis n k)⟫_ℂ
  have ha : HasSum a
      ((schrodingerThermalDensity unitOscillator (thermalRatio (ν 0)) (thermalRatio_mem (hν 0))).characteristic (q 0) (p 0)) :=
    hasSum_normalMixture_expect _ (thermalWeight_nonneg (thermalRatio_mem (hν 0)))
      (hasSum_thermalWeight (thermalRatio_mem (hν 0))) unitOscillatorBasis
      unitOscillatorBasis.orthonormal.norm_eq_one (weylOperator (q 0) (p 0))
  have hb : HasSum b
      ((canonicalThermalDensity (fun i : Fin n => ν i.succ) (fun i => hν i.succ)).characteristic
        (toLp 2 (fun i : Fin n => q i.succ)) (toLp 2 (fun i : Fin n => p i.succ))) :=
    canonicalThermalDensity_characteristic_hasSum _ _ _ _
  have hab := ha.mul hb (summable_mul_of_summable_norm (f := a) (g := b) ha.summable.norm hb.summable.norm)
  have he : (fun jk : ℕ × (Fin n → ℕ) => a jk.1*b jk.2) =
      (fun jk : ℕ × (Fin n → ℕ) => (occupationThermalWeight ν (Fin.cons jk.1 jk.2) : ℂ)*
        ⟪canonicalOscillatorBasis (n+1) (Fin.cons jk.1 jk.2),
          weyl q p (canonicalOscillatorBasis (n+1) (Fin.cons jk.1 jk.2))⟫_ℂ) := by
    funext jk
    rw [occupationThermalWeight_cons,canonicalOscillatorBasis_weyl_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Complex.ofReal_mul]
    dsimp only [a,b]
    ring
  apply (canonicalThermalDensity_characteristic_hasSum ν hν q p).unique
  apply (Fin.consEquiv (fun _ : Fin (n+1) => ℕ)).hasSum_iff.mp
  change HasSum (fun jk : ℕ × (Fin n → ℕ) => (occupationThermalWeight ν (Fin.cons jk.1 jk.2) : ℂ)*
    ⟪canonicalOscillatorBasis (n+1) (Fin.cons jk.1 jk.2),
      weyl q p (canonicalOscillatorBasis (n+1) (Fin.cons jk.1 jk.2))⟫_ℂ) _
  exact he ▸ hab

end Gaussian.Physical.Boson
