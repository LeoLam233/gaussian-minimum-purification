import Gaussian.Physical.Fermion.CutEntropy

noncomputable section
namespace Gaussian.Physical.Fermion

@[simp] theorem modeCountCast_rfl {n : ℕ} (ρ : Density n) : modeCountCast rfl ρ=ρ := rfl

@[simp] theorem modeCountCast_trans {n m l : ℕ} (h : n=m) (g : m=l) (ρ : Density n) :
    modeCountCast g (modeCountCast h ρ) = modeCountCast (h.trans g) ρ := by
  subst m
  subst l
  rfl

@[simp] theorem prefixRestriction_cast_aux (k l L : ℕ) (h : l+k=L+k) (ρ : Density (l+k)) :
    prefixRestriction k L (modeCountCast h ρ) = prefixRestriction k l ρ := by
  have haux : l=L := Nat.add_right_cancel h
  subst L
  rfl

end Gaussian.Physical.Fermion
