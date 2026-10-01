import Gaussian.Physical.Fermion.Restriction

noncomputable section
namespace Gaussian.Physical.Fermion

@[simp] theorem prefixIndex_val (k l : ℕ) (i : Fin k) : (prefixIndex k l i).val = i.val := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [prefixIndex_succ,Fin.val_succ,ih]

def doubledMajoranaEquiv (n : ℕ) : MajoranaIndex n ⊕ MajoranaIndex n ≃ MajoranaIndex (n+n) :=
  (Equiv.sumProdDistrib (Fin n) (Fin n) Bool).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl Bool))

@[simp] theorem doubledMajoranaEquiv_inl (n : ℕ) (a : MajoranaIndex n) :
    doubledMajoranaEquiv n (Sum.inl a) = (prefixIndex n n a.1,a.2) := by
  apply Prod.ext
  · apply Fin.ext
    simp [doubledMajoranaEquiv]
  · rfl

@[simp] theorem doubledMajoranaEquiv_symm_prefix (n : ℕ) (a : MajoranaIndex n) :
    (doubledMajoranaEquiv n).symm (prefixIndex n n a.1,a.2) = Sum.inl a := by
  rw [← doubledMajoranaEquiv_inl,Equiv.symm_apply_apply]

end Gaussian.Physical.Fermion
