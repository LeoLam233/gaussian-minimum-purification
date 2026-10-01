import Gaussian.Phase.Williamson

/-! Explicit squeezing factors for covariance-only bosonic purification.
The construction includes pure endpoints and never divides by a mixed defect. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase

/-- The hyperbolic cosine parameter, expressed without an inverse squeezing map. -/
def purificationCosh (ν : ℝ) : ℝ := Real.sqrt ((ν+1)/2)

/-- The hyperbolic sine parameter; it vanishes at the pure endpoint. -/
def purificationSinh (ν : ℝ) : ℝ := Real.sqrt ((ν-1)/2)

theorem purificationCosh_sq {ν : ℝ} (hν : 1 ≤ ν) : purificationCosh ν ^ 2 = (ν+1)/2 :=
  Real.sq_sqrt (by linarith)

theorem purificationSinh_sq {ν : ℝ} (hν : 1 ≤ ν) : purificationSinh ν ^ 2 = (ν-1)/2 :=
  Real.sq_sqrt (by linarith)

theorem purification_factor_difference {ν : ℝ} (hν : 1 ≤ ν) :
    purificationCosh ν ^ 2 - purificationSinh ν ^ 2 = 1 := by
  rw [purificationCosh_sq hν,purificationSinh_sq hν]
  ring

theorem purification_factor_sum {ν : ℝ} (hν : 1 ≤ ν) :
    purificationCosh ν ^ 2 + purificationSinh ν ^ 2 = ν := by
  rw [purificationCosh_sq hν,purificationSinh_sq hν]
  ring

@[simp] theorem purificationSinh_one : purificationSinh 1 = 0 := by simp [purificationSinh]

namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- A real scalar on each full mode, applied to both vectors of its paired frame. -/
def modeDiagonal (r : Fin n → ℝ) : E →ₗ[ℝ] E :=
  b.basis.toBasis.constr ℝ (fun i => r i.1 • b.basis i)

@[simp] theorem modeDiagonal_basis (r : Fin n → ℝ) (i : Fin n × Fin 2) :
    b.modeDiagonal r (b.basis i) = r i.1 • b.basis i :=
  b.basis.toBasis.constr_basis ℝ _ i

/-- Every real paired diagonal map is self-adjoint for the actual compatible metric. -/
theorem modeDiagonal_symmetric (r : Fin n → ℝ) : (b.modeDiagonal r).IsSymmetric := by
  have h : (innerₗ E).compl₁₂ (b.modeDiagonal r) LinearMap.id =
      (innerₗ E).compl₂ (b.modeDiagonal r) := by
    apply b.basis.toBasis.ext
    intro i
    apply b.basis.toBasis.ext
    intro j
    change ⟪b.modeDiagonal r (b.basis i),b.basis j⟫ =
      ⟪b.basis i,b.modeDiagonal r (b.basis j)⟫
    rw [b.modeDiagonal_basis,b.modeDiagonal_basis,inner_smul_left,inner_smul_right,
      b.basis.inner_eq_ite]
    split_ifs with hij
    · subst j; simp
    · simp
  intro x y
  exact congrArg (fun B : LinearMap.BilinForm ℝ E => B x y) h

/-- The paired diagonal map commutes with J even at degenerate parameters. -/
theorem modeDiagonal_commute_complex (r : Fin n → ℝ) (x : E) :
    J (b.modeDiagonal r x) = b.modeDiagonal r (J x) := by
  have h : J.linear.comp (b.modeDiagonal r) = (b.modeDiagonal r).comp J.linear := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change J (b.modeDiagonal r (b.basis (i,k))) = b.modeDiagonal r (J (b.basis (i,k)))
    fin_cases k
    · change J (b.modeDiagonal r (b.basis (i,0))) = b.modeDiagonal r (J (b.basis (i,0)))
      rw [b.modeDiagonal_basis,J.apply_smul,b.partner,b.modeDiagonal_basis]
    · change J (b.modeDiagonal r (b.basis (i,1))) = b.modeDiagonal r (J (b.basis (i,1)))
      rw [b.modeDiagonal_basis,J.apply_smul,b.partner_second,map_neg,b.modeDiagonal_basis]
      simp
  exact LinearMap.congr_fun h x

/-- Two paired scalar maps commute without a simple-spectrum assumption. -/
theorem modeDiagonal_commute (r s : Fin n → ℝ) (x : E) :
    b.modeDiagonal r (b.modeDiagonal s x) = b.modeDiagonal s (b.modeDiagonal r x) := by
  have h : (b.modeDiagonal r).comp (b.modeDiagonal s) =
      (b.modeDiagonal s).comp (b.modeDiagonal r) := by
    apply b.basis.toBasis.ext
    intro i
    change b.modeDiagonal r (b.modeDiagonal s (b.basis i)) =
      b.modeDiagonal s (b.modeDiagonal r (b.basis i))
    simp only [b.modeDiagonal_basis,map_smul,smul_smul]
    rw [mul_comm]
  exact LinearMap.congr_fun h x

/-- The scalar hyperbolic identity holds as an exact operator identity. -/
theorem modeDiagonal_squares_sub (r s : Fin n → ℝ) (h : ∀ i, r i ^ 2 - s i ^ 2 = 1)
    (x : E) : b.modeDiagonal r (b.modeDiagonal r x) -
      b.modeDiagonal s (b.modeDiagonal s x) = x := by
  have he : (b.modeDiagonal r).comp (b.modeDiagonal r) -
      (b.modeDiagonal s).comp (b.modeDiagonal s) = LinearMap.id := by
    apply b.basis.toBasis.ext
    intro i
    change b.modeDiagonal r (b.modeDiagonal r (b.basis i)) -
      b.modeDiagonal s (b.modeDiagonal s (b.basis i)) = b.basis i
    rw [b.modeDiagonal_basis,b.modeDiagonal_basis,map_smul,map_smul,
      b.modeDiagonal_basis,b.modeDiagonal_basis,smul_smul,smul_smul,← sub_smul]
    simpa only [pow_two,h,one_smul] using congrArg (fun q : ℝ => q • b.basis i) (h i.1)
  exact LinearMap.congr_fun he x

/-- The sum of squared squeezing factors recovers the actual amplitude K. -/
theorem modeDiagonal_squares_add (r s : Fin n → ℝ)
    (h : ∀ i, r i ^ 2 + s i ^ 2 = b.value i) (x : E) :
    b.modeDiagonal r (b.modeDiagonal r x) + b.modeDiagonal s (b.modeDiagonal s x) = K x := by
  have he : (b.modeDiagonal r).comp (b.modeDiagonal r) +
      (b.modeDiagonal s).comp (b.modeDiagonal s) = K := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change b.modeDiagonal r (b.modeDiagonal r (b.basis (i,k))) +
      b.modeDiagonal s (b.modeDiagonal s (b.basis (i,k))) = K (b.basis (i,k))
    rw [b.modeDiagonal_basis,b.modeDiagonal_basis,map_smul,map_smul,
      b.modeDiagonal_basis,b.modeDiagonal_basis,smul_smul,smul_smul,← add_smul,b.eigen]
    exact congrArg (fun q : ℝ => q • b.basis (i,k)) (by simpa only [pow_two] using h i)
  exact LinearMap.congr_fun he x

end PairedEigenframe
end Gaussian.Phase
