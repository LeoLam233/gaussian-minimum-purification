import Gaussian.Physical.Boson.FourierUniqueness
import Gaussian.Physical.Boson.Thermal
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Completeness

/-! Unconditional full oscillator Hilbert basis. L1 Fourier uniqueness bypasses the upstream
pointwise Plancherel premise. No occupation truncation is used. -/
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory FourierTransform
open QuantumMechanics.OneDimension
open scoped InnerProductSpace FourierTransform

theorem oscillator_zero_of_orthogonal_mk (Q : HarmonicOscillator)
    (f : ℝ → ℂ) (hf : QuantumMechanics.OneDimension.HilbertSpace.MemHS f)
    (hOrth : ∀ k : ℕ, ⟪QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k),
      QuantumMechanics.OneDimension.HilbertSpace.mk hf⟫_ℂ = 0) :
    QuantumMechanics.OneDimension.HilbertSpace.mk hf = 0 := by
  have hξ := Q.ξ_pos
  have he : (fun x => f x * ↑(Real.exp (-x^2/(2*Q.ξ^2)))) =
      (fun x => f x * ↑(Real.exp (-(1/(2*Q.ξ^2))*(x-0)^2))) := by
    funext x
    simp only [sub_zero]
    congr 3
    ring
  have hint : Integrable (fun x => f x * ↑(Real.exp (-x^2/(2*Q.ξ^2)))) := by
    rw [he]
    exact memLp_one_iff_integrable.mp
      (QuantumMechanics.OneDimension.HilbertSpace.mul_gaussian_mem_Lp_one f hf
        (1/(2*Q.ξ^2)) 0 (by positivity))
  have hz := ae_eq_zero_of_fourier_eq_zero hint
    (Q.fourierIntegral_zero_of_mem_orthogonal f hf hOrth)
  have hfe : f =ᵐ[volume] 0 := by
    filter_upwards [hz] with x hx
    simpa only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero,
      Real.exp_ne_zero, or_false] using hx
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact (QuantumMechanics.OneDimension.HilbertSpace.coe_mk_ae hf).trans hfe

theorem oscillator_dense_span (Q : HarmonicOscillator) :
    (Submodule.span ℂ (Set.range (fun k =>
      QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k)))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  obtain ⟨g, hg, rfl⟩ := QuantumMechanics.OneDimension.HilbertSpace.mk_surjective f
  apply oscillator_zero_of_orthogonal_mk Q g hg
  intro k
  rw [Submodule.mem_orthogonal'] at hf
  rw [← inner_conj_symm]
  have h := hf (QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k))
    (Submodule.subset_span (Set.mem_range_self k))
  simp only [h, map_zero]

def oscillatorBasis (Q : HarmonicOscillator) :
    HilbertBasis ℕ ℂ QuantumMechanics.OneDimension.HilbertSpace :=
  HilbertBasis.mk Q.eigenfunction_orthonormal (by rw [oscillator_dense_span Q])

@[simp] theorem oscillatorBasis_apply (Q : HarmonicOscillator) (k : ℕ) :
    oscillatorBasis Q k = QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k) :=
  congrFun (HilbertBasis.coe_mk Q.eigenfunction_orthonormal _) k

def schrodingerThermalDensity (Q : HarmonicOscillator) (r : ℝ)
    (hr : r ∈ Set.Ico (0:ℝ) 1) : NormalDensity QuantumMechanics.OneDimension.HilbertSpace :=
  normalMixture (thermalWeight r) (thermalWeight_nonneg hr) (hasSum_thermalWeight hr)
    (oscillatorBasis Q) (oscillatorBasis Q).orthonormal.norm_eq_one

theorem schrodingerThermalDensity_eigenvector (Q : HarmonicOscillator) (r : ℝ)
    (hr : r ∈ Set.Ico (0:ℝ) 1) (k : ℕ) :
    (schrodingerThermalDensity Q r hr).operator.1
      (QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k)) =
      (thermalWeight r k : ℂ) • QuantumMechanics.OneDimension.HilbertSpace.mk (Q.eigenfunction_memHS k) := by
  unfold schrodingerThermalDensity
  simpa only [oscillatorBasis_apply] using normalMixture_eigenvector
    (thermalWeight r) (thermalWeight_nonneg hr) (hasSum_thermalWeight hr) (oscillatorBasis Q) k

end Gaussian.Physical.Boson
