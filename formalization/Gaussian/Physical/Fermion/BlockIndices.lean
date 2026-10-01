import Gaussian.Physical.Fermion.DoubledIndices

set_option maxHeartbeats 10000
set_option trace.profiler true
noncomputable section
namespace Gaussian.Physical.Fermion

/-- Concatenate complete physical and auxiliary mode labels, physical modes first. -/
def blockMajoranaEquiv (k l : ℕ) : MajoranaIndex k ⊕ MajoranaIndex l ≃ MajoranaIndex (l+k) :=
  (Equiv.sumProdDistrib (Fin k) (Fin l) Bool).symm.trans
    (Equiv.prodCongr ((finSumFinEquiv (m := k) (n := l)).trans (finCongr (Nat.add_comm k l))) (Equiv.refl Bool))

@[simp] theorem blockMajoranaEquiv_inl (k l : ℕ) (a : MajoranaIndex k) :
    blockMajoranaEquiv k l (Sum.inl a) = (prefixIndex k l a.1,a.2) := by
  apply Prod.ext
  · apply Fin.ext
    change a.1.val = (prefixIndex k l a.1).val
    rw [prefixIndex_val k l a.1]
  · rfl

@[simp] theorem blockMajoranaEquiv_symm_prefix (k l : ℕ) (a : MajoranaIndex k) :
    (blockMajoranaEquiv k l).symm (prefixIndex k l a.1,a.2) = Sum.inl a := by
  rw [← blockMajoranaEquiv_inl k l a,Equiv.symm_apply_apply]

end Gaussian.Physical.Fermion
