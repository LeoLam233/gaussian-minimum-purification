import Gaussian.Physical.Boson.ProductConfiguration

/-! The concrete real configuration reordering AB,A′B′ to AA′,BB′. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
open WithLp
open scoped InnerProductSpace
variable (A B C D : Type*)
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D]

def fourConfigFlatten :
    JointConfiguration (JointConfiguration A B) (JointConfiguration C D) ≃ₗ[ℝ] ((A×B)×(C×D)) :=
  (WithLp.linearEquiv 2 ℝ ((JointConfiguration A B)×(JointConfiguration C D))).trans
    ((WithLp.linearEquiv 2 ℝ (A×B)).prodCongr (WithLp.linearEquiv 2 ℝ (C×D)))

def fourPartyLinear :
    JointConfiguration (JointConfiguration A B) (JointConfiguration C D) ≃ₗ[ℝ]
      JointConfiguration (JointConfiguration A C) (JointConfiguration B D) :=
  ((fourConfigFlatten A B C D).trans (LinearEquiv.prodProdProdComm ℝ A B C D)).trans
    (fourConfigFlatten A C B D).symm

theorem fourPartyLinear_inner
    (x y : JointConfiguration (JointConfiguration A B) (JointConfiguration C D)) :
    ⟪fourPartyLinear A B C D x,fourPartyLinear A B C D y⟫_ℝ=⟪x,y⟫_ℝ := by
  simp [fourPartyLinear,fourConfigFlatten,WithLp.prod_inner_apply,
    add_assoc,add_left_comm,add_comm]

def fourPartyReorder :
    JointConfiguration (JointConfiguration A B) (JointConfiguration C D) ≃ₗᵢ[ℝ]
      JointConfiguration (JointConfiguration A C) (JointConfiguration B D) :=
  (fourPartyLinear A B C D).isometryOfInner (fourPartyLinear_inner A B C D)

@[simp] theorem fourPartyReorder_apply
    (x : JointConfiguration (JointConfiguration A B) (JointConfiguration C D)) :
    fourPartyReorder A B C D x=
      toLp 2 (toLp 2 ((ofLp (ofLp x).1).1,(ofLp (ofLp x).2).1),
        toLp 2 ((ofLp (ofLp x).1).2,(ofLp (ofLp x).2).2)) := rfl

@[simp] theorem fourPartyReorder_symm_apply
    (x : JointConfiguration (JointConfiguration A C) (JointConfiguration B D)) :
    (fourPartyReorder A B C D).symm x=
      toLp 2 (toLp 2 ((ofLp (ofLp x).1).1,(ofLp (ofLp x).2).1),
        toLp 2 ((ofLp (ofLp x).1).2,(ofLp (ofLp x).2).2)) := rfl

end Gaussian.Physical.Boson
