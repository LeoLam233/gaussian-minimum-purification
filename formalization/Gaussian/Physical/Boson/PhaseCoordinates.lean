import Gaussian.Physical.Boson.CanonicalCovariance
import Gaussian.Physical.Boson.WeylSymplectic

/-! Concrete q/p bases with the same Boolean mode orientation as the independent covariance cost. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Module
open scoped RealInnerProductSpace

/-- Left coordinates are q (false), right coordinates p (true). -/
def phaseSumEquiv (ι : Type*) : (ι ⊕ ι) ≃ (ι × Bool) where
  toFun := Sum.elim (fun i => (i,false)) (fun i => (i,true))
  invFun x := if x.2 then Sum.inr x.1 else Sum.inl x.1
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i,b⟩; cases b <;> rfl

def phaseBasis {ι E : Type*} [AddCommGroup E] [Module ℝ E] (b : Basis ι ℝ E) :
    Basis (ι × Bool) ℝ (E×E) := (b.prod b).reindex (phaseSumEquiv ι)

@[simp] lemma phaseBasis_false {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Basis ι ℝ E) (i : ι) : phaseBasis b (i,false)=(b i,0) := by
  rw [phaseBasis, Basis.reindex_apply]
  change (b.prod b) (Sum.inl i)=(b i,0)
  simp only [Basis.prod_apply,Sum.elim_inl,Function.comp_apply,LinearMap.inl_apply]

@[simp] lemma phaseBasis_true {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Basis ι ℝ E) (i : ι) : phaseBasis b (i,true)=(0,b i) := by
  rw [phaseBasis, Basis.reindex_apply]
  change (b.prod b) (Sum.inr i)=(0,b i)
  simp only [Basis.prod_apply,Sum.elim_inr,Function.comp_apply,LinearMap.inr_apply]

lemma phaseBasis_commutator {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (i j : ι × Bool) :
    weylSymplecticForm E (phaseBasis b.toBasis i) (phaseBasis b.toBasis j)=
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1) else (if j.2 then 1 else 0)) else 0 := by
  rcases i with ⟨i,bi⟩
  rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> by_cases hij : i=j <;>
    simp [weylSymplecticForm_apply,orthonormal_iff_ite.mp b.orthonormal,hij]

def canonicalPhaseBasis (n : ℕ) :
    Basis (Fin n × Bool) ℝ (CanonicalConfiguration n × CanonicalConfiguration n) :=
  phaseBasis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

lemma canonicalPhaseBasis_commutator (n : ℕ) (i j : Fin n × Bool) :
    weylSymplecticForm (CanonicalConfiguration n) (canonicalPhaseBasis n i) (canonicalPhaseBasis n j)=
      if i.1=j.1 then (if i.2 then (if j.2 then 0 else -1) else (if j.2 then 1 else 0)) else 0 :=
  phaseBasis_commutator (EuclideanSpace.basisFun (Fin n) ℝ) i j

lemma canonicalPhaseBasis_covariance {n : ℕ} (ν : Fin n → ℝ) (i j : Fin n × Bool) :
    canonicalCovariance ν (canonicalPhaseBasis n i) (canonicalPhaseBasis n j)=
      if i=j then ν i.1 else 0 := by
  classical
  rcases i with ⟨i,bi⟩
  rcases j with ⟨j,bj⟩
  cases bi <;> cases bj <;> by_cases hij : i=j <;>
    simp [canonicalPhaseBasis,canonicalCovariance_apply,EuclideanSpace.basisFun_apply,
      PiLp.single_apply,mul_ite,ite_mul,hij] <;>
    simp_all only [ne_eq, not_false_eq_true, false_implies, eq_comm]

end Gaussian.Physical.Boson
