import Gaussian.Analysis.HilbertBasisTotality

/-! Transport and reindexing of actual complete Hilbert bases. -/
noncomputable section
namespace Gaussian.Analysis
open scoped InnerProductSpace
variable {ι κ H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def mapHilbertBasis (b : HilbertBasis ι ℂ H) (U : H ≃ₗᵢ[ℂ] K) : HilbertBasis ι ℂ K :=
  HilbertBasis.ofRepr (U.symm.trans b.repr)

@[simp] lemma mapHilbertBasis_apply (b : HilbertBasis ι ℂ H) (U : H ≃ₗᵢ[ℂ] K) (i : ι) :
    mapHilbertBasis b U i=U (b i) := by
  classical
  change U (b.repr.symm (lp.single 2 i (1:ℂ)))=U (b i)
  rw [b.repr_symm_single]

def reindexHilbertBasis (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) : HilbertBasis κ ℂ H := by
  classical
  refine HilbertBasis.mkOfOrthogonalEqBot (v := fun i : κ => b (e.symm i)) ?_ ?_
  · rw [orthonormal_iff_ite]
    intro i j
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp only [e.symm.injective.eq_iff]
  · apply le_antisymm ?_ bot_le
    intro x hx
    change x=0
    apply b.repr.injective
    ext i
    have h := hx (b i) (Submodule.subset_span ⟨e i,by simp⟩)
    simpa [HilbertBasis.repr_apply_apply] using h

@[simp] lemma reindexHilbertBasis_apply (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) (i : κ) :
    reindexHilbertBasis b e i=b (e.symm i) := by
  simp only [reindexHilbertBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

end Gaussian.Analysis
