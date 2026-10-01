import Gaussian.Physical.Fermion.SidewiseLiftCoordinates
import Gaussian.Physical.Fermion.SidewiseComplement

/-! Lift an actual local AA' Gaussian action to the full purifier while fixing
all AB Majoranas.  Global coordinates are returned to canonical AB,A',B' order. -/
noncomputable section
namespace Gaussian.Physical.Fermion

theorem initialBasis_fixed_of_castLE (a k : ℕ) (ha : a≤k)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (hfix : ∀ i : MajoranaIndex a,R (coefficientBasis k (Fin.castLE ha i.1,i.2))=
      coefficientBasis k (Fin.castLE ha i.1,i.2)) :
    ∀ i : MajoranaIndex k,i.1.val<a → R (coefficientBasis k i)=coefficientBasis k i := by
  rintro ⟨i,b⟩ hi
  have he : Fin.castLE ha (⟨i.val,hi⟩ : Fin a)=i := by apply Fin.ext; rfl
  simpa only [he] using hfix (⟨i.val,hi⟩,b)

theorem sidewiseRestriction_working_count (nA nB mA mB k : ℕ)
    (hk : nA+mA=k) (hN : (mA+mB)+(nA+nB)=(nB+mB)+k)
    (ρ : Density ((mA+mB)+(nA+nB))) :
    modeCountCast hk (sidewiseRestriction nA nB mA mB ρ)=
      prefixRestriction k (nB+mB) (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))) :=
  prefixRestriction_cast_retained_eq hk _ hN _

theorem sidewiseComplement_working_count (nA nB mA mB k : ℕ)
    (hk : nA+mA=k) (hN : (mA+mB)+(nA+nB)=(nB+mB)+k)
    (ρ : Density ((mA+mB)+(nA+nB))) :
    sidewiseComplementRestriction nA nB mA mB ρ=
      suffixRestriction k (nB+mB) (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))) :=
  suffixRestriction_cast_prefix_eq hk _ hN _

/-- Every local AA' orthogonal action fixing its physical A vectors lifts to
an actual global CAR unitary fixing all physical AB vectors. -/
theorem exists_sidewise_local_lift (nA nB mA mB k : ℕ) (hk : nA+mA=k)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (U : Matrix.unitaryGroup (Occupation k) ℂ) (hU : Implements k R U)
    (hfix : ∀ a : MajoranaIndex k,a.1.val<nA → R (coefficientBasis k a)=coefficientBasis k a) :
    ∃ (Q : CoefficientSpace ((mA+mB)+(nA+nB)) ≃ₗᵢ[ℝ] CoefficientSpace ((mA+mB)+(nA+nB)))
      (W : Matrix.unitaryGroup (Occupation ((mA+mB)+(nA+nB))) ℂ),
      Implements ((mA+mB)+(nA+nB)) Q W ∧
      (∀ a : MajoranaIndex (nA+nB),Q (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2))=
        coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2)) ∧
      ∀ ρ : Density ((mA+mB)+(nA+nB)),IsQuasifree ρ →
        prefixRestriction (nA+nB) (mA+mB) (ρ.uConj W)=prefixRestriction (nA+nB) (mA+mB) ρ ∧
        modeCountCast hk (sidewiseRestriction nA nB mA mB (ρ.uConj W))=
          (modeCountCast hk (sidewiseRestriction nA nB mA mB ρ)).uConj U ∧
        sidewiseComplementRestriction nA nB mA mB (ρ.uConj W)=sidewiseComplementRestriction nA nB mA mB ρ := by
  have hN : (mA+mB)+(nA+nB)=(nB+mB)+k := by omega
  obtain ⟨V,hV⟩ := orthogonal_implemented ((nB+mB)+k) (localCutLift k (nB+mB) R)
  let Q := (sidewiseRotation nA nB mA mB)⁻¹ *
    orthogonalCountCast hN.symm (localCutLift k (nB+mB) R) * sidewiseRotation nA nB mA mB
  let W := (sidewiseUnitary nA nB mA mB)⁻¹ * unitaryCountCast hN.symm V * sidewiseUnitary nA nB mA mB
  have hQ : Implements ((mA+mB)+(nA+nB)) Q W :=
    implements_mul _ (implements_mul _ (implements_inv _ (sidewiseUnitary_implements nA nB mA mB))
      (implements_countCast hN.symm _ V hV)) (sidewiseUnitary_implements nA nB mA mB)
  have hQfix (a : MajoranaIndex (nA+nB)) :
      Q (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2))=
        coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2) := by
    have hw := localCutLift_fixes_working_physical nA nB mA mB k hk hN R hfix a
    have hb := (orthogonalCountCast_fix_iff hN (localCutLift k (nB+mB) R)
      (sidewiseRotation nA nB mA mB (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2)))).mpr hw
    change (sidewiseRotation nA nB mA mB).symm
      (orthogonalCountCast hN.symm (localCutLift k (nB+mB) R)
        (sidewiseRotation nA nB mA mB (coefficientBasis _ (prefixIndex (nA+nB) (mA+mB) a.1,a.2)))) = _
    rw [hb,LinearIsometryEquiv.symm_apply_apply]
  refine ⟨Q,W,hQ,hQfix,?_⟩
  intro ρ hρ
  have hWork : modeCountCast hN ((ρ.uConj W).uConj (sidewiseUnitary nA nB mA mB)) =
      (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))).uConj V := by
    dsimp only [W]
    rw [unitaryState_conjugated_action,modeCountCast_unitaryState,unitaryCountCast_trans,unitaryCountCast_rfl]
  have hχ : IsQuasifree (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))) :=
    modeCountCast_isQuasifree hN _ (isQuasifree_unitary_of_implements _ ρ hρ _ _
      (sidewiseUnitary_implements nA nB mA mB))
  refine ⟨implemented_fixed_prefix_marginal (nA+nB) (mA+mB) ρ Q W hQ hQfix,?_,?_⟩
  · calc
      _ = prefixRestriction k (nB+mB) (modeCountCast hN ((ρ.uConj W).uConj (sidewiseUnitary nA nB mA mB))) :=
        sidewiseRestriction_working_count nA nB mA mB k hk hN _
      _ = prefixRestriction k (nB+mB) ((modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))).uConj V) := by rw [hWork]
      _ = (prefixRestriction k (nB+mB) (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB)))).uConj U :=
        localCutLift_prefix_density k (nB+mB) _ hχ R U hU V hV
      _ = _ := congrArg (fun δ => δ.uConj U) (sidewiseRestriction_working_count nA nB mA mB k hk hN ρ).symm
  · calc
      _ = suffixRestriction k (nB+mB) (modeCountCast hN ((ρ.uConj W).uConj (sidewiseUnitary nA nB mA mB))) :=
        sidewiseComplement_working_count nA nB mA mB k hk hN _
      _ = suffixRestriction k (nB+mB) ((modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))).uConj V) := by rw [hWork]
      _ = suffixRestriction k (nB+mB) (modeCountCast hN (ρ.uConj (sidewiseUnitary nA nB mA mB))) :=
        localCutLift_suffix_density k (nB+mB) _ hχ R V hV
      _ = _ := (sidewiseComplement_working_count nA nB mA mB k hk hN ρ).symm

/-- Local cut rotations preserve the exact physical purifier domain and cost. -/
theorem exists_sidewise_local_state (nA nB mA mB k : ℕ) (hk : nA+mA=k)
    (ρ : Density (nA+nB)) (σ : Density ((mA+mB)+(nA+nB)))
    (hσ : IsSidewisePurifier nA nB mA mB ρ σ)
    (R : CoefficientSpace k ≃ₗᵢ[ℝ] CoefficientSpace k)
    (U : Matrix.unitaryGroup (Occupation k) ℂ) (hU : Implements k R U)
    (hfix : ∀ a : MajoranaIndex k,a.1.val<nA → R (coefficientBasis k a)=coefficientBasis k a) :
    ∃ τ : Density ((mA+mB)+(nA+nB)),IsSidewisePurifier nA nB mA mB ρ τ ∧
      modeCountCast hk (sidewiseRestriction nA nB mA mB τ)=
        (modeCountCast hk (sidewiseRestriction nA nB mA mB σ)).uConj U ∧
      sidewiseComplementRestriction nA nB mA mB τ=sidewiseComplementRestriction nA nB mA mB σ ∧
      sidewiseEntropy nA nB mA mB τ=sidewiseEntropy nA nB mA mB σ := by
  obtain ⟨Q,W,hW,hfixW,hact⟩ := exists_sidewise_local_lift nA nB mA mB k hk R U hU hfix
  obtain ⟨hm,hp,hs⟩ := hact σ hσ.1.1
  refine ⟨σ.uConj W,⟨⟨isQuasifree_unitary_of_implements _ σ hσ.1.1 Q W hW,
    (unitaryState_pure_iff σ W).mpr hσ.1.2⟩,hm.trans hσ.2⟩,hp,hs,?_⟩
  unfold sidewiseEntropy
  rw [← modeCountCast_entropy hk (sidewiseRestriction nA nB mA mB (σ.uConj W)),hp,
    unitaryState_entropy,modeCountCast_entropy]

end Gaussian.Physical.Fermion
