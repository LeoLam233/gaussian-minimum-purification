import Gaussian.Physical.Fermion.LocalCutLift
import Gaussian.Physical.Fermion.CountedActionTransport

noncomputable section
namespace Gaussian.Physical.Fermion

/-- Forward physical labels in the AA',BB' working chart. -/
theorem sidewiseModePermutation_physical_val (nA nB mA mB : ℕ) (i : Fin (nA+nB)) :
    (sidewiseModePermutation nA nB mA mB (prefixIndex (nA+nB) (mA+mB) i)).val =
      if i.val<nA then i.val else i.val+mA := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have he : prefixIndex (nA+nB) (mA+mB) (Fin.castAdd nB a) =
        fourModeEquiv nA nB mA mB (Sum.inl (Sum.inl a)) := by
      apply Fin.ext
      simp [fourModeEquiv]
    rw [he]
    simp [sidewiseModePermutation,fourModeEquiv,Equiv.sumSumSumComm,a.isLt]
  · have he : prefixIndex (nA+nB) (mA+mB) (Fin.natAdd nA b) =
        fourModeEquiv nA nB mA mB (Sum.inl (Sum.inr b)) := by
      apply Fin.ext
      simp [fourModeEquiv]
    rw [he]
    have hb : ¬nA+b.val<nA := by omega
    simp [sidewiseModePermutation,fourModeEquiv,Equiv.sumSumSumComm,hb]
    omega

@[simp] theorem sidewiseRotation_basis (nA nB mA mB : ℕ)
    (a : MajoranaIndex ((mA+mB)+(nA+nB))) :
    sidewiseRotation nA nB mA mB (coefficientBasis _ a) =
      coefficientBasis _ (sidewiseModePermutation nA nB mA mB a.1,a.2) := by
  rcases a with ⟨i,b⟩
  simp [sidewiseRotation,coefficientBasis,reindexCoefficient_single]

/-- A local AA' action fixing its first physical A directions fixes every
physical AB direction after lifting and passage to the working chart. -/
theorem localCutLift_fixes_working_physical (nA nB mA mB k : ℕ)
    (hk : nA+mA=k) (hN : (mA+mB)+(nA+nB)=(nB+mB)+k)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (hfix : ∀ a : MajoranaIndex k,a.1.val<nA → R (coefficientBasis k a)=coefficientBasis k a)
    (a : MajoranaIndex (nA+nB)) :
    localCutLift k (nB+mB) R
      (coefficientCountEquiv hN (sidewiseRotation nA nB mA mB
        (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2)))) =
      coefficientCountEquiv hN (sidewiseRotation nA nB mA mB
        (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2))) := by
  rw [sidewiseRotation_basis,coefficientCountEquiv_basis]
  let z : MajoranaIndex ((nB+mB)+k) :=
    (Fin.cast hN (sidewiseModePermutation nA nB mA mB (prefixIndex (nA+nB) (mA+mB) a.1)),a.2)
  change localCutLift k (nB+mB) R (coefficientBasis _ z)=coefficientBasis _ z
  have hz : z.1.val=if a.1.val<nA then a.1.val else a.1.val+mA := by
    simp only [z,Fin.val_cast,sidewiseModePermutation_physical_val]
  by_cases ha : a.1.val<nA
  · let j : Fin k := ⟨a.1.val,by omega⟩
    have he : z=(prefixIndex k (nB+mB) j,a.2) := by
      apply Prod.ext
      · apply Fin.ext
        rw [prefixIndex_val]
        simpa only [j,if_pos ha] using hz
      · rfl
    rw [he]
    exact localCutLift_prefix_fixed k (nB+mB) R (j,a.2) (hfix (j,a.2) ha)
  · let j : Fin (nB+mB) := ⟨a.1.val-nA,by have h := a.1.isLt; omega⟩
    have he : z=(suffixIndex k (nB+mB) j,a.2) := by
      apply Prod.ext
      · apply Fin.ext
        rw [suffixIndex_val]
        change z.1.val=k+(a.1.val-nA)
        rw [hz,if_neg ha]
        omega
      · rfl
    rw [he]
    exact localCutLift_suffix_basis k (nB+mB) R (j,a.2)

end Gaussian.Physical.Fermion
