import Gaussian.Physical.Boson.WeylImplementation

/-! Closure of the proved concrete Weyl implementation relation under actual
unitary composition and inversion. -/
set_option autoImplicit false
noncomputable section
namespace Gaussian.Physical.Boson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem WeylImplements.trans {R S : (E×E) ≃ₗ[ℝ] (E×E)}
    {U V : unitary (Schrodinger E →L[ℂ] Schrodinger E)}
    (hR : WeylImplements R U) (hS : WeylImplements S V) :
    WeylImplements (R.trans S) (U*V) := by
  intro z
  calc
    _ = star (V : Schrodinger E →L[ℂ] Schrodinger E) *
        (star (U : Schrodinger E →L[ℂ] Schrodinger E)*weylOperator z.1 z.2*U)*V := by
      change star ((U : Schrodinger E →L[ℂ] Schrodinger E)*(V : Schrodinger E →L[ℂ] Schrodinger E))*
        weylOperator z.1 z.2*((U : Schrodinger E →L[ℂ] Schrodinger E)*(V : Schrodinger E →L[ℂ] Schrodinger E)) = _
      simp only [star_mul,mul_assoc]
    _ = star (V : Schrodinger E →L[ℂ] Schrodinger E)*weylOperator (R z).1 (R z).2*V := by
      rw [hR z]
    _ = _ := hS (R z)

theorem WeylImplements.symm {R : (E×E) ≃ₗ[ℝ] (E×E)}
    {U : unitary (Schrodinger E →L[ℂ] Schrodinger E)} (hR : WeylImplements R U) :
    WeylImplements R.symm (star U) := by
  intro z
  have h := congrArg (fun T : Schrodinger E →L[ℂ] Schrodinger E =>
    (U : Schrodinger E →L[ℂ] Schrodinger E)*T*star (U : Schrodinger E →L[ℂ] Schrodinger E))
    (hR (R.symm z))
  have hu := Unitary.mul_star_self_of_mem U.property
  have hu' := Unitary.star_mul_self_of_mem U.property
  simp only [R.apply_symm_apply] at h
  have hh : (weylOperator (R.symm z).1 (R.symm z).2 : Schrodinger E →L[ℂ] Schrodinger E) =
      (U : Schrodinger E →L[ℂ] Schrodinger E)*weylOperator z.1 z.2*
        star (U : Schrodinger E →L[ℂ] Schrodinger E) := by
    calc
      _ = (U : Schrodinger E →L[ℂ] Schrodinger E) *
          (star (U : Schrodinger E →L[ℂ] Schrodinger E)*
            weylOperator (R.symm z).1 (R.symm z).2*U)*
          star (U : Schrodinger E →L[ℂ] Schrodinger E) := by
        calc
          _ = ((U : Schrodinger E →L[ℂ] Schrodinger E)*star (U : Schrodinger E →L[ℂ] Schrodinger E))*
            weylOperator (R.symm z).1 (R.symm z).2*
            ((U : Schrodinger E →L[ℂ] Schrodinger E)*star (U : Schrodinger E →L[ℂ] Schrodinger E)) := by rw [hu,one_mul,mul_one]
          _ = _ := by simp only [mul_assoc]
      _ = _ := h
  change star (star (U : Schrodinger E →L[ℂ] Schrodinger E))*weylOperator z.1 z.2*
    star (U : Schrodinger E →L[ℂ] Schrodinger E) = _
  simpa only [star_star] using hh.symm

end Gaussian.Physical.Boson
