import Gaussian.Physical.Boson.ProductConfiguration
import Gaussian.Physical.Boson.ConfigurationIsometry

/-! Concrete canonical finite configuration spaces and their exact one-mode/tail decomposition. -/
noncomputable section
namespace Gaussian.Physical.Boson
open WithLp
open scoped RealInnerProductSpace

abbrev CanonicalConfiguration (n : ℕ) := EuclideanSpace ℝ (Fin n)

def euclideanConsLinear (n : ℕ) :
    JointConfiguration ℝ (CanonicalConfiguration n) ≃ₗ[ℝ] CanonicalConfiguration (n+1) where
  toFun z := toLp 2 (Fin.cons (ofLp z).1 (ofLp (ofLp z).2))
  invFun z := toLp 2 (z 0,toLp 2 (fun i : Fin n => z i.succ))
  left_inv z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply WithLp.ofLp_injective 2
      funext i
      rfl
  right_inv z := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' z w := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r z := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma euclideanConsLinear_inner (n : ℕ) (x y : JointConfiguration ℝ (CanonicalConfiguration n)) :
    ⟪euclideanConsLinear n x,euclideanConsLinear n y⟫=⟪x,y⟫ := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ,WithLp.prod_inner_apply,PiLp.inner_apply]
  rfl

def euclideanConsIsometry (n : ℕ) :
    JointConfiguration ℝ (CanonicalConfiguration n) ≃ₗᵢ[ℝ] CanonicalConfiguration (n+1) where
  __ := euclideanConsLinear n
  norm_map' x := by
    have h := euclideanConsLinear_inner n x x
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (euclideanConsLinear n x),norm_nonneg x]

@[simp] lemma euclideanConsIsometry_apply_zero (n : ℕ)
    (x : JointConfiguration ℝ (CanonicalConfiguration n)) : euclideanConsIsometry n x 0=(ofLp x).1 := rfl

@[simp] lemma euclideanConsIsometry_apply_succ (n : ℕ)
    (x : JointConfiguration ℝ (CanonicalConfiguration n)) (i : Fin n) :
    euclideanConsIsometry n x i.succ=(ofLp x).2 i := rfl

@[simp] lemma euclideanConsIsometry_symm (n : ℕ) (x : CanonicalConfiguration (n+1)) :
    (euclideanConsIsometry n).symm x=toLp 2 (x 0,toLp 2 (fun i : Fin n => x i.succ)) := rfl

end Gaussian.Physical.Boson
