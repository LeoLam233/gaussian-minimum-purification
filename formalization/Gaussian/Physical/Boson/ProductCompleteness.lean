import Gaussian.Physical.Boson.ProductWeyl
import Gaussian.Physical.Boson.SchrodingerNontrivial
import Gaussian.Physical.Boson.WeylInjectivity
import Gaussian.Analysis.HilbertBasisTotality

/-! Completeness of the actual product Hilbert basis. The proof uses the
independently proved trace-class Weyl separation theorem on a genuine rank-one
operator. Weyl separation itself does not use this product-basis construction. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory ProbabilisticTheory
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem eq_zero_of_jointProduct_orthogonal (ψ : Schrodinger (JointConfiguration E F))
    (h : ∀ (f : Schrodinger E) (g : Schrodinger F), ⟪jointProduct f g,ψ⟫_ℂ=0) : ψ=0 := by
  obtain ⟨f,hf⟩ := exists_nonzero_schrodinger (E := E)
  obtain ⟨g,hg⟩ := exists_nonzero_schrodinger (E := F)
  have hp : ‖jointProduct f g‖≠0 := by
    rw [jointProduct_norm]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hf) (norm_ne_zero_iff.mpr hg)
  have hz : outerOperator ψ (jointProduct f g)=0 := by
    apply traceClass_eq_zero_of_weyl_zero
    intro q p
    rw [tracePairing_outerOperator]
    calc
      _ = ⟪star (weylOperator q p : Schrodinger (JointConfiguration E F) →L[ℂ]
          Schrodinger (JointConfiguration E F)) (jointProduct f g),ψ⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
      _ = 0 := by
        rw [weylOperator_star]
        change ⟪weyl (-q) (-p) (jointProduct f g),ψ⟫_ℂ=0
        rw [weyl_jointProduct]
        exact h _ _
  have hn := congrArg norm hz
  rw [norm_outerOperator,norm_zero] at hn
  exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right hp)

theorem eq_zero_of_jointProduct_basis_orthogonal {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F))
    (ψ : Schrodinger (JointConfiguration E F))
    (h : ∀ i j, ⟪jointProduct (b i) (c j),ψ⟫_ℂ=0) : ψ=0 := by
  have hj (j : κ) : ∀ f : Schrodinger E, ⟪jointProduct f (c j),ψ⟫_ℂ=0 :=
    Gaussian.Analysis.inner_image_zero_of_basis b (jointProductEmbedding (c j)) ψ (fun i => h i j)
  apply eq_zero_of_jointProduct_orthogonal ψ
  intro f
  exact Gaussian.Analysis.inner_image_zero_of_basis c (jointProductEmbeddingLeft f) ψ (fun j => hj j f)

theorem jointProduct_orthonormal {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F)) :
    Orthonormal ℂ (fun ij : ι×κ => jointProduct (b ij.1) (c ij.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [jointProduct_inner,(orthonormal_iff_ite.mp b.orthonormal),
    (orthonormal_iff_ite.mp c.orthonormal)]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [h1,h2,Prod.ext_iff]

def jointProductBasis {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F)) :
    HilbertBasis (ι×κ) ℂ (Schrodinger (JointConfiguration E F)) :=
  HilbertBasis.mkOfOrthogonalEqBot (jointProduct_orthonormal b c) (by
    apply le_antisymm ?_ bot_le
    intro ψ hψ
    change ψ=0
    apply eq_zero_of_jointProduct_basis_orthogonal b c ψ
    intro i j
    exact hψ _ (Submodule.subset_span ⟨(i,j),rfl⟩))

@[simp] theorem jointProductBasis_apply {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Schrodinger E)) (c : HilbertBasis κ ℂ (Schrodinger F)) (i : ι) (j : κ) :
    jointProductBasis b c (i,j)=jointProduct (b i) (c j) := by
  simp only [jointProductBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

end Gaussian.Physical.Boson
