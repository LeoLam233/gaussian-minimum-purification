import Gaussian.Phase.BosonicPurificationBlocks

/-! An explicit auxiliary orientation reversal in the actual paired Williamson
frame. This is a coefficient-space map, not a claim about a unitary implementer. -/
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace Gaussian.Phase
namespace PairedEigenframe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {J : OrthogonalComplexStructure E} {K : E →ₗ[ℝ] E} {n : ℕ}
  (b : PairedEigenframe J K n)

/-- Fix each first paired vector and negate its partner. -/
def reflectionMap : E →ₗ[ℝ] E :=
  b.basis.toBasis.constr ℝ (fun i => if i.2 = 0 then b.basis i else -b.basis i)

@[simp] theorem reflectionMap_basis_zero (i : Fin n) :
    b.reflectionMap (b.basis (i,0)) = b.basis (i,0) := by
  change b.basis.toBasis.constr ℝ _ (b.basis.toBasis (i,0)) = _
  rw [Basis.constr_basis]
  simp

@[simp] theorem reflectionMap_basis_one (i : Fin n) :
    b.reflectionMap (b.basis (i,1)) = -b.basis (i,1) := by
  change b.basis.toBasis.constr ℝ _ (b.basis.toBasis (i,1)) = _
  rw [Basis.constr_basis]
  simp

theorem reflectionMap_square (x : E) : b.reflectionMap (b.reflectionMap x) = x := by
  have h : b.reflectionMap.comp b.reflectionMap = LinearMap.id := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change b.reflectionMap (b.reflectionMap (b.basis (i,k))) = b.basis (i,k)
    fin_cases k <;> simp
  exact LinearMap.congr_fun h x

theorem reflectionMap_inner (x y : E) :
    ⟪b.reflectionMap x,b.reflectionMap y⟫ = ⟪x,y⟫ := by
  have h : (innerₗ E).compl₁₂ b.reflectionMap b.reflectionMap = innerₗ E := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    apply b.basis.toBasis.ext
    rintro ⟨j,l⟩
    change ⟪b.reflectionMap (b.basis (i,k)),b.reflectionMap (b.basis (j,l))⟫ =
      ⟪b.basis (i,k),b.basis (j,l)⟫
    fin_cases k <;> fin_cases l <;> simp [b.basis.inner_eq_ite]
  exact congrArg (fun B : LinearMap.BilinForm ℝ E => B x y) h

/-- The orientation change is an actual orthogonal equivalence in the
compatible metric, including the empty and degenerate-parameter cases. -/
def reflection : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective (b.reflectionMap.isometryOfInner b.reflectionMap_inner)
    (fun x => ⟨b.reflectionMap x,b.reflectionMap_square x⟩)

@[simp] theorem reflection_apply (x : E) : b.reflection x = b.reflectionMap x := rfl

@[simp] theorem reflection_basis_zero (i : Fin n) :
    b.reflection (b.basis (i,0)) = b.basis (i,0) := b.reflectionMap_basis_zero i

@[simp] theorem reflection_basis_one (i : Fin n) :
    b.reflection (b.basis (i,1)) = -b.basis (i,1) := b.reflectionMap_basis_one i

/-- The explicit coordinate reflection anticommutes with the actual J. -/
theorem reflection_anticommute (x : E) : J (b.reflection x) = -b.reflection (J x) := by
  have h : J.linear.comp b.reflectionMap = -(b.reflectionMap.comp J.linear) := by
    apply b.basis.toBasis.ext
    rintro ⟨i,k⟩
    change J (b.reflectionMap (b.basis (i,k))) = -b.reflectionMap (J (b.basis (i,k)))
    fin_cases k
    · change J (b.reflectionMap (b.basis (i,0))) = -b.reflectionMap (J (b.basis (i,0)))
      rw [b.reflectionMap_basis_zero,b.partner,b.reflectionMap_basis_one,neg_neg]
    · change J (b.reflectionMap (b.basis (i,1))) = -b.reflectionMap (J (b.basis (i,1)))
      rw [b.reflectionMap_basis_one,J.apply_neg,b.partner_second,map_neg,
        b.reflectionMap_basis_zero,neg_neg]
  exact LinearMap.congr_fun h x

/-- The opposite auxiliary commutator is converted to the original sign by
this proved map; the sign identification is never assumed by naming. -/
theorem reflection_antisymplectic (x y : E) :
    J.symplecticForm (b.reflection x) (b.reflection y) = -J.symplecticForm x y := by
  simp only [OrthogonalComplexStructure.symplecticForm_apply]
  rw [b.reflection_anticommute,inner_neg_right,b.reflection.inner_map_map,neg_neg]

end PairedEigenframe
end Gaussian.Phase
