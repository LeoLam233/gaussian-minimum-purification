import Gaussian.Physical.Fermion.Factorization

/-! Pure marginal factorization for arbitrary finite density matrices. The joint
state need not be pure or quasifree. CAR use requires the separate signed
subsystem-identification theorems. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Fermion
variable {d e f : Type*} [Fintype d] [Fintype e] [Fintype f]
  [DecidableEq d] [DecidableEq e] [DecidableEq f]

theorem traceRight_assoc (ρ : MState ((d×e)×f)) :
    (ρ.relabel (Equiv.prodAssoc d e f).symm).traceRight = ρ.traceRight.traceRight := by
  apply MState.ext_m
  ext i j
  change (∑ z : e×f,ρ.m ((i,z.1),z.2) ((j,z.1),z.2)) =
    ∑ a : e,∑ b : f,ρ.m ((i,a),b) ((j,a),b)
  exact Fintype.sum_prod_type _

theorem traceRight_assoc_product (ρ : MState d) (σ : MState (e×f)) :
    ((ρ.prod σ).relabel (Equiv.prodAssoc d e f)).traceRight = ρ.prod σ.traceRight := by
  apply MState.ext_m
  ext ⟨i,a⟩ ⟨j,b⟩
  change (∑ c : f,ρ.m i j*σ.m (a,c) (b,c)) = ρ.m i j*(∑ c : f,σ.m (a,c) (b,c))
  exact (Finset.mul_sum _ _ _).symm

/-- A pure left marginal factors from every actual finite density extension. -/
theorem density_factors_of_pure_left (ρ : MState (d×e))
    (hl : ∃ φ,ρ.traceRight=MState.pure φ) :
    ρ=ρ.traceRight.prod ρ.traceLeft := by
  let χ : MState (d×(e×(d×e))) := (MState.pure ρ.purify).relabel (Equiv.prodAssoc d e (d×e)).symm
  have hχp : ∃ ψ,χ=MState.pure ψ := MState.relabel_pure_exists ρ.purify _
  have hχa : χ.traceRight=ρ.traceRight := by
    dsimp only [χ]
    rw [traceRight_assoc,ρ.purify_spec]
  have hχfactor := pure_density_factors_of_pure_left χ hχp (by rw [hχa]; exact hl)
  have hr : (χ.relabel (Equiv.prodAssoc d e (d×e))).traceRight=ρ := by
    simp only [χ,MState.relabel_relabel,Equiv.self_trans_symm,MState.relabel_refl,ρ.purify_spec]
  have he : ρ=ρ.traceRight.prod χ.traceLeft.traceRight := by
    calc
      ρ=(χ.relabel (Equiv.prodAssoc d e (d×e))).traceRight := hr.symm
      _=((χ.traceRight.prod χ.traceLeft).relabel (Equiv.prodAssoc d e (d×e))).traceRight :=
        congrArg (fun τ : MState (d×(e×(d×e))) =>
          (τ.relabel (Equiv.prodAssoc d e (d×e))).traceRight) hχfactor
      _=χ.traceRight.prod χ.traceLeft.traceRight := traceRight_assoc_product _ _
      _=ρ.traceRight.prod χ.traceLeft.traceRight := by rw [hχa]
  have hb : ρ.traceLeft=χ.traceLeft.traceRight := by rw [he,MState.traceLeft_prod_eq]
  rw [hb]
  exact he

/-- A pure right marginal likewise factors, with no purity premise on the joint state. -/
theorem density_factors_of_pure_right (ρ : MState (d×e))
    (hr : ∃ φ,ρ.traceLeft=MState.pure φ) :
    ρ=ρ.traceRight.prod ρ.traceLeft := by
  have hs := density_factors_of_pure_left ρ.SWAP (by simpa using hr)
  have he := congrArg MState.SWAP hs
  rw [MState.SWAP_SWAP,MState.traceRight_SWAP,MState.traceLeft_SWAP] at he
  calc
    ρ=(ρ.traceLeft.prod ρ.traceRight).SWAP := he
    _=ρ.traceRight.prod ρ.traceLeft := by
      apply MState.ext_m
      ext ⟨i,j⟩ ⟨k,l⟩
      change ρ.traceLeft.m j l*ρ.traceRight.m i k=ρ.traceRight.m i k*ρ.traceLeft.m j l
      exact mul_comm _ _

end Gaussian.Physical.Fermion
