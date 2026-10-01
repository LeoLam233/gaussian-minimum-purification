import Gaussian.Phase.BosonicPurificationProduct

/-! Actual auxiliary symplectic covariance orbits between two independently
presented finite auxiliary spaces. Degenerate coupling and zero dimensions are
included; only raw pure covariances and exact physical restrictions are used. -/
noncomputable section
open Module
namespace Gaussian.Phase
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

/-- Equal physical covariance and equal auxiliary dimension give an actual
auxiliary symplectic equivalence transporting the complete pure covariance. -/
theorem exists_pure_covariance_auxiliary_equiv
    (Ω : LinearMap.BilinForm ℝ E) (σ : LinearMap.BilinForm ℝ F)
    (τ : LinearMap.BilinForm ℝ G) (hΩ : Ω.Nondegenerate)
    (p : PureCompatibleCovariance (productForm Ω σ))
    (q : PureCompatibleCovariance (productForm Ω τ))
    (hd : finrank ℝ F = finrank ℝ G)
    (hphys : ∀ x y, p.form (x,0) (y,0) = q.form (x,0) (y,0)) :
    ∃ Q : F ≃ₗ[ℝ] G,
      (∀ x y, τ (Q x) (Q y) = σ x y) ∧
      (∀ a b x y, q.form (a,Q x) (b,Q y) = p.form (a,x) (b,y)) := by
  obtain ⟨R,hR,hRJ,hRg⟩ := exists_raw_metric_intertwiner p.form q.form
    p.symmetric q.symmetric p.positive q.positive p.generator q.generator
    p.square_neg q.square_neg p.metric_isometry q.metric_isometry
    (LinearMap.inl ℝ E F) (LinearMap.inl ℝ E G)
    (by simp only [Module.finrank_prod,hd]) hphys (by
      intro x y
      rw [p.compatible,q.compatible,p.symplectic,q.symplectic]
      simp)
  have hRΩ : ∀ x y, productForm Ω τ (R x) (R y) = productForm Ω σ x y := by
    intro x y
    have h := hRg x (p.generator y)
    rw [q.compatible,p.compatible,hRJ,q.square_neg,p.square_neg,map_neg,map_neg] at h
    exact neg_injective h
  have hfix : ∀ a : E, R (a,0) = (a,0) := hR
  have hfix' : ∀ a : E, R.symm (a,0) = (a,0) := by
    intro a
    apply R.injective
    rw [R.apply_symm_apply,hfix]
  have hf : ∀ x : F, (R (0,x)).1 = 0 := by
    intro x
    apply hΩ.2
    intro a
    have h := hRΩ (a,0) (0,x)
    rw [hfix] at h
    simpa using h
  have hg : ∀ y : G, (R.symm (0,y)).1 = 0 := by
    intro y
    apply hΩ.2
    intro a
    have h := hRΩ (a,0) (R.symm (0,y))
    rw [hfix,R.apply_symm_apply] at h
    simpa using h.symm
  have haux : ∀ x : F, R (0,x) = (0,(R (0,x)).2) := by
    intro x
    exact Prod.ext (hf x) rfl
  have haux' : ∀ y : G, R.symm (0,y) = (0,(R.symm (0,y)).2) := by
    intro y
    exact Prod.ext (hg y) rfl
  let Q : F ≃ₗ[ℝ] G :=
    { toLinearMap := (LinearMap.snd ℝ E G).comp (R.toLinearMap.comp (LinearMap.inr ℝ E F))
      invFun := fun y => (R.symm (0,y)).2
      left_inv := fun x => by
        change (R.symm (0,(R (0,x)).2)).2 = x
        have h := congrArg Prod.snd (R.symm_apply_apply (0,x))
        rw [haux] at h
        exact h
      right_inv := fun y => by
        change (R (0,(R.symm (0,y)).2)).2 = y
        have h := congrArg Prod.snd (R.apply_symm_apply (0,y))
        rw [haux'] at h
        exact h }
  have hcoords : ∀ (a : E) (x : F), R (a,x) = (a,Q x) := by
    intro a x
    calc
      R (a,x) = R ((a,0)+(0,x)) := by simp
      _ = R (a,0) + R (0,x) := R.map_add _ _
      _ = (a,Q x) := by rw [hfix,haux]; simp [Q]
  refine ⟨Q,?_,?_⟩
  · intro x y
    have h := hRΩ (0,x) (0,y)
    rw [hcoords,hcoords] at h
    simpa using h
  · intro a b x y
    have h := hRg (a,x) (b,y)
    rw [hcoords,hcoords] at h
    exact h

end Gaussian.Phase
