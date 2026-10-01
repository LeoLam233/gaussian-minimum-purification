import Gaussian.Physical.Boson.ProductVectors
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Bounded product-vector embeddings and their actual Hilbert adjoints. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory
open scoped InnerProductSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

def productEmbedding (g : Lp ℂ 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  ({ toFun := fun f => productVector f g
     map_add' := by
       intro f f'
       apply Lp.ext
       have ht := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add f f')
       filter_upwards [productVector_ae (f+f') g,productVector_ae f g,productVector_ae f' g,ht,
         Lp.coeFn_add (productVector f g) (productVector f' g)] with z h1 h2 h3 h4 h5
       simp only [Function.comp_apply,Pi.add_apply] at h4
       rw [h1,h5,h4]
       simp only [Pi.add_apply,h2,h3,add_mul]
     map_smul' := by
       intro c f
       change productVector (c • f) g=c • productVector f g
       apply Lp.ext
       have ht := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c f)
       filter_upwards [productVector_ae (c • f) g,productVector_ae f g,ht,
         Lp.coeFn_smul c (productVector f g)] with z h1 h2 h3 h4
       simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul] at h3
       rw [h1,h4,h3]
       simp only [Pi.smul_apply,smul_eq_mul,h2,mul_assoc] } :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 (μ.prod ν)).mkContinuous ‖g‖ (fun f => by
      change ‖productVector f g‖≤‖g‖*‖f‖
      rw [productVector_norm,mul_comm])

/-- The bounded embedding with the left factor fixed. -/
def productEmbeddingLeft (f : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  ({ toFun := fun g => productVector f g
     map_add' := by
       intro g g'
       apply Lp.ext
       have ht := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add g g')
       filter_upwards [productVector_ae f (g+g'),productVector_ae f g,productVector_ae f g',ht,
         Lp.coeFn_add (productVector f g) (productVector f g')] with z h1 h2 h3 h4 h5
       simp only [Function.comp_apply,Pi.add_apply] at h4
       rw [h1,h5,h4]
       simp only [Pi.add_apply,h2,h3,mul_add]
     map_smul' := by
       intro c g
       change productVector f (c • g)=c • productVector f g
       apply Lp.ext
       have ht := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c g)
       filter_upwards [productVector_ae f (c • g),productVector_ae f g,ht,
         Lp.coeFn_smul c (productVector f g)] with z h1 h2 h3 h4
       simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul] at h3
       rw [h1,h4,h3]
       simp only [Pi.smul_apply,smul_eq_mul,h2,mul_left_comm] } :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν)).mkContinuous ‖f‖ (fun g => by
      change ‖productVector f g‖≤‖f‖*‖g‖
      rw [productVector_norm])

@[simp] theorem productEmbeddingLeft_apply (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productEmbeddingLeft f g=productVector f g := rfl

@[simp] theorem productEmbedding_apply (g : Lp ℂ 2 ν) (f : Lp ℂ 2 μ) :
    productEmbedding g f=productVector f g := rfl

def productExtraction (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 μ :=
  (productEmbedding g).adjoint

theorem productExtraction_inner (g : Lp ℂ 2 ν) (f : Lp ℂ 2 μ) (u : Lp ℂ 2 (μ.prod ν)) :
    ⟪f,productExtraction g u⟫_ℂ=⟪productVector f g,u⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (productEmbedding g) f u

theorem productExtraction_product (g g' : Lp ℂ 2 ν) (f : Lp ℂ 2 μ) :
    productExtraction g (productVector f g')=⟪g,g'⟫_ℂ • f := by
  apply ext_inner_left ℂ
  intro h
  rw [productExtraction_inner,productVector_inner,inner_smul_right,mul_comm]

def productIsometry (g : Lp ℂ 2 ν) (hg : ‖g‖=1) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) where
  __ := (productEmbedding g).toLinearMap
  norm_map' f := by
    change ‖productVector f g‖=‖f‖
    rw [productVector_norm,hg,mul_one]

end Gaussian.Physical.Boson
