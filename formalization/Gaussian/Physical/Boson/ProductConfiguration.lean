import Gaussian.Physical.Boson.L2MeasureEquiv
import Gaussian.Physical.Boson.ProductEmbedding
import Gaussian.Physical.Boson.Weyl

/-! The concrete Schroedinger product configuration and its actual product vectors. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open MeasureTheory WithLp
open scoped InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

abbrev JointConfiguration (E F : Type*) := WithLp 2 (E×F)

def productConfigurationUnitary :
    Lp ℂ 2 ((volume : Measure E).prod (volume : Measure F)) ≃ₗᵢ[ℂ]
      Schrodinger (JointConfiguration E F) :=
  l2MeasureEquiv (MeasurableEquiv.toLp 2 (E×F)).symm
    (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E F)

def jointProduct (f : Schrodinger E) (g : Schrodinger F) :
    Schrodinger (JointConfiguration E F) := productConfigurationUnitary (productVector f g)

theorem jointProduct_ae (f : Schrodinger E) (g : Schrodinger F) :
    jointProduct f g =ᵐ[volume] fun z => f (ofLp z).1*g (ofLp z).2 := by
  have ht := (WithLp.volume_preserving_ofLp E F).quasiMeasurePreserving.ae_eq_comp (productVector_ae f g)
  filter_upwards [l2MeasureEquiv_ae (MeasurableEquiv.toLp 2 (E×F)).symm
      (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E F) (productVector f g),ht] with x h1 h2
  exact h1.trans h2

theorem jointProduct_inner (f f' : Schrodinger E) (g g' : Schrodinger F) :
    ⟪jointProduct f g,jointProduct f' g'⟫_ℂ=⟪f,f'⟫_ℂ*⟪g,g'⟫_ℂ := by
  rw [jointProduct,jointProduct,LinearIsometryEquiv.inner_map_map,productVector_inner]

theorem jointProduct_norm (f : Schrodinger E) (g : Schrodinger F) :
    ‖jointProduct f g‖=‖f‖*‖g‖ := by
  rw [jointProduct,LinearIsometryEquiv.norm_map,productVector_norm]

def jointProductEmbedding (g : Schrodinger F) :
    Schrodinger E →L[ℂ] Schrodinger (JointConfiguration E F) :=
  (productConfigurationUnitary (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.comp (productEmbedding g)

def jointProductEmbeddingLeft (f : Schrodinger E) :
    Schrodinger F →L[ℂ] Schrodinger (JointConfiguration E F) :=
  (productConfigurationUnitary (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.comp (productEmbeddingLeft f)

@[simp] theorem jointProductEmbedding_apply (g : Schrodinger F) (f : Schrodinger E) :
    jointProductEmbedding g f=jointProduct f g := rfl

@[simp] theorem jointProductEmbeddingLeft_apply (f : Schrodinger E) (g : Schrodinger F) :
    jointProductEmbeddingLeft f g=jointProduct f g := rfl

end Gaussian.Physical.Boson
