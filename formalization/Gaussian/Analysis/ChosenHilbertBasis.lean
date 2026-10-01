import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A basis choice obtained from the proved Hilbert-basis existence theorem.
It adds no mathematical assumption and will disappear from basis-independent reductions. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Analysis
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def chosenHilbertBasisSet : Set H := Classical.choose (exists_hilbertBasis ℂ H)

def chosenHilbertBasis : HilbertBasis (chosenHilbertBasisSet H) ℂ H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))

end Gaussian.Analysis
