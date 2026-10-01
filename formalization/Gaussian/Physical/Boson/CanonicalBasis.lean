import Gaussian.Physical.Boson.EmptyConfiguration
import Gaussian.Physical.Boson.UnitOscillator
import Gaussian.Physical.Boson.ProductCompleteness
import Gaussian.Analysis.HilbertBasisTransport

/-! A genuine complete oscillator Hilbert basis on every finite canonical configuration space.
The full occupation index is Fin n→Nat; no cutoff or multidimensional sorryful basis is imported. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Gaussian.Physical.Boson
open Gaussian.Analysis WithLp
open scoped InnerProductSpace

def canonicalOscillatorBasis : (n : ℕ) → HilbertBasis (Fin n → ℕ) ℂ (Schrodinger (CanonicalConfiguration n))
  | 0 => emptyOccupationBasis
  | n+1 => reindexHilbertBasis
      (mapHilbertBasis (jointProductBasis unitOscillatorBasis (canonicalOscillatorBasis n))
        (schrodingerIsometry (euclideanConsIsometry n)))
      (Fin.consEquiv (fun _ : Fin (n+1) => ℕ))

@[simp] lemma canonicalOscillatorBasis_zero (k : Fin 0 → ℕ) :
    canonicalOscillatorBasis 0 k=emptyVacuum := emptyOccupationBasis_apply k

lemma canonicalOscillatorBasis_succ (n : ℕ) (k : Fin (n+1) → ℕ) :
    canonicalOscillatorBasis (n+1) k = schrodingerIsometry (euclideanConsIsometry n)
      (jointProduct (unitOscillatorBasis (k 0))
        (canonicalOscillatorBasis n (fun i : Fin n => k i.succ))) := by
  rw [canonicalOscillatorBasis,reindexHilbertBasis_apply,mapHilbertBasis_apply]
  change schrodingerIsometry (euclideanConsIsometry n)
    (jointProductBasis unitOscillatorBasis (canonicalOscillatorBasis n) (k 0,fun i : Fin n => k i.succ))=_
  rw [jointProductBasis_apply]

/-- The actual diagonal Weyl coefficient factors into one mode and the true remaining product. -/
theorem canonicalOscillatorBasis_weyl_succ (n : ℕ) (k : Fin (n+1) → ℕ)
    (q p : CanonicalConfiguration (n+1)) :
    ⟪canonicalOscillatorBasis (n+1) k,weyl q p (canonicalOscillatorBasis (n+1) k)⟫_ℂ =
      ⟪unitOscillatorBasis (k 0),weyl (q 0) (p 0) (unitOscillatorBasis (k 0))⟫_ℂ *
      ⟪canonicalOscillatorBasis n (fun i : Fin n => k i.succ),
        weyl (toLp 2 (fun i : Fin n => q i.succ)) (toLp 2 (fun i : Fin n => p i.succ))
          (canonicalOscillatorBasis n (fun i : Fin n => k i.succ))⟫_ℂ := by
  rw [canonicalOscillatorBasis_succ]
  let e := euclideanConsIsometry n
  let f := jointProduct (unitOscillatorBasis (k 0))
    (canonicalOscillatorBasis n (fun i : Fin n => k i.succ))
  have h := schrodingerIsometry_weyl e (e.symm q) (e.symm p) f
  rw [e.apply_symm_apply,e.apply_symm_apply] at h
  rw [← h,LinearIsometryEquiv.inner_map_map,weyl_jointProduct,jointProduct_inner]
  rfl

end Gaussian.Physical.Boson
