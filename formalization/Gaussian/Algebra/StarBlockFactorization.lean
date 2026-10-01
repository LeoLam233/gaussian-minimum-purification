import Gaussian.Algebra.SymplecticPivot

/-! Exact star-ring Schur identities behind the symplectic shear factorization.
Invertibility is supplied only for the pivoted block, whose existence is proved separately. -/
noncomputable section
namespace Gaussian.Algebra
variable {R : Type*} [Ring R] [StarRing R]

/-- An invertible upper-left symplectic block gives two genuinely self-adjoint shear coefficients
and the exact lower-right Schur identity. -/
theorem star_block_schur {A B C D A' : R}
    (hAA' : A*A'=1) (hA'A : A'*A=1)
    (hAC : star A*C=star C*A) (hBD : star B*D=star D*B)
    (hAD : star A*D-star C*B=1) :
    star (C*A')=C*A' ∧ star (A'*B)=A'*B ∧ D=(C*A')*B+star A' := by
  have hstar : star A'*star A=1 := by simpa only [star_mul,star_one] using congrArg star hAA'
  have hl (x : R) : star A'*(star A*x)=x := by rw [← mul_assoc,hstar,one_mul]
  have hr (x : R) : (x*A)*A'=x := by rw [mul_assoc,hAA',mul_one]
  have hK : star (C*A')=C*A' := by
    have h := congrArg (fun x : R => star A'*x*A') hAC
    rw [hl,← mul_assoc (star A') (star C) A,hr] at h
    simpa only [star_mul] using h.symm
  have hK' : star A'*star C=C*A' := by simpa only [star_mul] using hK
  have hD : D=(C*A')*B+star A' := by
    have h := congrArg (fun x : R => star A'*x) hAD
    simp only [mul_sub,mul_one] at h
    rw [hl,← mul_assoc (star A') (star C) B,hK'] at h
    calc
      D = (D-(C*A')*B)+(C*A')*B := by abel
      _ = star A'+(C*A')*B := by rw [h]
      _ = (C*A')*B+star A' := add_comm _ _
  have hN : star (A'*B)=A'*B := by
    have h := hBD
    rw [hD,star_add,star_mul,star_star,hK,mul_add,add_mul] at h
    have hh : (star B*(C*A'))*B+star B*star A' =
        (star B*(C*A'))*B+A'*B := by simpa only [mul_assoc] using h
    simpa only [star_mul] using add_left_cancel hh
  exact ⟨hK,hN,hD⟩

end Gaussian.Algebra
