import Gaussian.Physical.Boson.CanonicalGaussianOn
import Gaussian.Physical.Boson.WilliamsonCoordinates

/-! A genuine symplectic equivalence from a raw Williamson basis to a canonical
configuration basis; both original bilinear forms are transported exactly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma canonicalPhaseCoordinates_basis {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (i : Fin n × Bool) :
    canonicalPhaseCoordinates a.repr (phaseBasis a.toBasis i)=canonicalPhaseBasis n i := by
  rcases i with ⟨i,c⟩
  cases c <;> simp [canonicalPhaseCoordinates,canonicalPhaseBasis,
    OrthonormalBasis.repr_self,EuclideanSpace.basisFun_apply]

lemma canonicalCovarianceOn_basis {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (ν : Fin n → ℝ) (i j : Fin n × Bool) :
    canonicalCovarianceOn a.repr ν (phaseBasis a.toBasis i) (phaseBasis a.toBasis j)=
      if i=j then ν i.1 else 0 := by
  change canonicalCovariance ν (canonicalPhaseCoordinates a.repr (phaseBasis a.toBasis i))
    (canonicalPhaseCoordinates a.repr (phaseBasis a.toBasis j))=_
  rw [canonicalPhaseCoordinates_basis,canonicalPhaseCoordinates_basis,canonicalPhaseBasis_covariance]

/-- The equivalence sends each actual Williamson vector to its canonical q or p vector. -/
def normalFormEquiv {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n × Bool) ℝ (E×E)) : (E×E) ≃ₗ[ℝ] (E×E) :=
  b.equiv (phaseBasis a.toBasis) (Equiv.refl _)

@[simp] lemma normalFormEquiv_basis {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n × Bool) ℝ (E×E)) (i : Fin n × Bool) :
    normalFormEquiv a b (b i)=phaseBasis a.toBasis i := by
  exact Basis.equiv_apply _ _ _ _

theorem normalFormEquiv_symplectic {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n × Bool) ℝ (E×E))
    (hbΩ : ∀ i j, weylSymplecticForm E (b i) (b j)=
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1)
        else (if j.2 then 1 else 0)) else 0) :
    ∀ z w, weylSymplecticForm E (normalFormEquiv a b z) (normalFormEquiv a b w)=
      weylSymplecticForm E z w := by
  have he : (weylSymplecticForm E).compl₁₂ (normalFormEquiv a b).toLinearMap
      (normalFormEquiv a b).toLinearMap=weylSymplecticForm E := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change weylSymplecticForm E (normalFormEquiv a b (b i)) (normalFormEquiv a b (b j))=_
    rw [normalFormEquiv_basis,normalFormEquiv_basis,phaseBasis_commutator,hbΩ]
  intro z w
  exact congrArg (fun B : LinearMap.BilinForm ℝ (E×E) => B z w) he

theorem normalFormEquiv_covariance {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n × Bool) ℝ (E×E)) (V : LinearMap.BilinForm ℝ (E×E))
    (ν : Fin n → ℝ) (hbV : ∀ i j, V (b i) (b j)=if i=j then ν i.1 else 0) :
    (canonicalCovarianceOn a.repr ν).compl₁₂ (normalFormEquiv a b).toLinearMap
      (normalFormEquiv a b).toLinearMap=V := by
  apply b.ext
  intro i
  apply b.ext
  intro j
  change canonicalCovarianceOn a.repr ν (normalFormEquiv a b (b i)) (normalFormEquiv a b (b j))=_
  rw [normalFormEquiv_basis,normalFormEquiv_basis,canonicalCovarianceOn_basis,hbV]

end Gaussian.Physical.Boson
