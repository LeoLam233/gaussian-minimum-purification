import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Explicit scalar product summation, keeping function arguments opaque during
elaboration of later operator-valued expectation applications. -/
set_option autoImplicit false
namespace Gaussian.Analysis
variable {𝕜 : Type*} [NormedCommRing 𝕜] [NormedSpace ℝ 𝕜]
  [FiniteDimensional ℝ 𝕜] [CompleteSpace 𝕜]

theorem hasSum_scalar_product {ι κ : Type*} (f : ι → 𝕜) (g : κ → 𝕜) (a b : 𝕜)
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : ι×κ => f ij.1*g ij.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm (f := f) (g := g) hf.summable.norm hg.summable.norm)

end Gaussian.Analysis
