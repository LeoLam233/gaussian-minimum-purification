import Gaussian.Phase.Restriction
import Gaussian.Phase.AdaptationTransport

noncomputable section
open Module Gaussian.Spectral
open scoped RealInnerProductSpace
namespace Gaussian.Phase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A J-invariant coefficient cut inherits a proved skew adaptation with the
actual positive amplitude compression; no K-invariance is required. -/
def SkewAdaptationData.compressed {T : E →ₗ[ℝ] E} (d : SkewAdaptationData T)
    (U : Submodule ℝ E) (hU : d.complexStructure.IsInvariant U) :
    SkewAdaptationData (compression T U) where
  J := (d.complexStructure.restrict U hU).linear
  K := compression d.K U
  square_neg := (d.complexStructure.restrict U hU).square_neg
  skew := (d.complexStructure.restrict U hU).inner_map_left
  positive := by
    refine ⟨compression_symmetric d.positive.isSymmetric U,?_⟩
    intro x
    have h := d.positive.inner_nonneg_right (x : E)
    rw [← inner_compression (T := d.K) U x x] at h
    simpa only [RCLike.re_to_real, real_inner_comm] using h
  factor := d.complexStructure.compression_factor U hU d.factor
  commute := d.complexStructure.compression_commute U hU d.K d.commute

end Gaussian.Phase
