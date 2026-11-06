import Yamabe3.Analysis.NativeCollarScalarMultiplier

/-! Literal second-order coefficient multiplication on the same collar
jet. Its H2-jet to L2 bound is linear in the true coefficient bound; no
higher Sobolev regularity or derivative of the input is presumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar

def nativeCollarJetValueCLM : NativeCollarJet →L[ℝ] NativeCollarL2 := ContinuousLinearMap.fst ℝ _ _
def nativeCollarJetFirstCLM (j : Fin 3) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
def nativeCollarJetSecondCLM (k j : Fin 3) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  (ContinuousLinearMap.proj j : (Fin 3 → NativeCollarL2) →L[ℝ] NativeCollarL2).comp
    ((ContinuousLinearMap.proj k : (Fin 3 → Fin 3 → NativeCollarL2) →L[ℝ] (Fin 3 → NativeCollarL2)).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))

variable (a : Fin 3 → Fin 3 → E → ℝ) (b : Fin 3 → E → ℝ) (c : E → ℝ)
  (ha : ∀ i j,Continuous (a i j)) (hb : ∀ j,Continuous (b j)) (hc : Continuous c)

def nativeCollarJetPerturbationCLM : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  (∑ i : Fin 3,∑ j : Fin 3,(nativeCollarScalarMulCLM (a i j) (ha i j)).comp (nativeCollarJetSecondCLM i j))+
    (∑ j : Fin 3,(nativeCollarScalarMulCLM (b j) (hb j)).comp (nativeCollarJetFirstCLM j))+
    (nativeCollarScalarMulCLM c hc).comp nativeCollarJetValueCLM

theorem nativeCollarJetPerturbationCLM_apply (J : NativeCollarJet) :
    nativeCollarJetPerturbationCLM a b c ha hb hc J=
      (∑ i : Fin 3,∑ j : Fin 3,nativeCollarScalarMulCLM (a i j) (ha i j) (J.2.2 i j))+
      (∑ j : Fin 3,nativeCollarScalarMulCLM (b j) (hb j) (J.2.1 j))+nativeCollarScalarMulCLM c hc J.1 := by
  simp [nativeCollarJetPerturbationCLM,nativeCollarJetFirstCLM,nativeCollarJetSecondCLM,nativeCollarJetValueCLM]

theorem nativeCollarJetPerturbationCLM_norm_le {η : ℝ} (hη : 0≤η)
    (haη : ∀ x ∈ nativePoissonEntranceCollar,∀ i j,‖a i j x‖≤η)
    (hbη : ∀ x ∈ nativePoissonEntranceCollar,∀ j,‖b j x‖≤η)
    (hcη : ∀ x ∈ nativePoissonEntranceCollar,‖c x‖≤η) (J : NativeCollarJet) :
    ‖nativeCollarJetPerturbationCLM a b c ha hb hc J‖≤(13*η)*‖J‖ := by
  have hJ0 : ‖J.1‖≤‖J‖ := norm_fst_le J
  have hJ1 (j : Fin 3) : ‖J.2.1 j‖≤‖J‖ :=
    (norm_le_pi_norm J.2.1 j).trans ((norm_fst_le J.2).trans (norm_snd_le J))
  have hJ2 (i j : Fin 3) : ‖J.2.2 i j‖≤‖J‖ :=
    (norm_le_pi_norm (J.2.2 i) j).trans ((norm_le_pi_norm J.2.2 i).trans ((norm_snd_le J.2).trans (norm_snd_le J)))
  have hA (i j : Fin 3) : ‖nativeCollarScalarMulCLM (a i j) (ha i j) (J.2.2 i j)‖≤η*‖J‖ :=
    (nativeCollarScalarMulCLM_norm_le (a i j) (ha i j) hη (fun x hx => haη x hx i j) _).trans
      (mul_le_mul_of_nonneg_left (hJ2 i j) hη)
  have hB (j : Fin 3) : ‖nativeCollarScalarMulCLM (b j) (hb j) (J.2.1 j)‖≤η*‖J‖ :=
    (nativeCollarScalarMulCLM_norm_le (b j) (hb j) hη (fun x hx => hbη x hx j) _).trans
      (mul_le_mul_of_nonneg_left (hJ1 j) hη)
  have hC : ‖nativeCollarScalarMulCLM c hc J.1‖≤η*‖J‖ :=
    (nativeCollarScalarMulCLM_norm_le c hc hη hcη _).trans (mul_le_mul_of_nonneg_left hJ0 hη)
  rw [nativeCollarJetPerturbationCLM_apply]
  calc
    _ ≤ ((∑ i : Fin 3,∑ j : Fin 3,‖nativeCollarScalarMulCLM (a i j) (ha i j) (J.2.2 i j)‖)+
        (∑ j : Fin 3,‖nativeCollarScalarMulCLM (b j) (hb j) (J.2.1 j)‖))+
        ‖nativeCollarScalarMulCLM c hc J.1‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_add_le _ _).trans
      exact add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))) (norm_sum_le _ _)
    _ ≤ ((∑ _i : Fin 3,∑ _j : Fin 3,η*‖J‖)+(∑ _j : Fin 3,η*‖J‖))+η*‖J‖ :=
      add_le_add (add_le_add (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hA i j)))
        (Finset.sum_le_sum (fun j _ => hB j))) hC
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat];ring

private theorem collar_sum_ae (f : Fin 3 → NativeCollarL2) :
    (⇑(∑ i : Fin 3,f i))=ᵐ[volume.restrict nativePoissonEntranceCollar] (fun x => ∑ i : Fin 3,(f i : E → ℝ) x) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ f] with x hx
  simpa only [Finset.sum_apply] using hx

theorem nativeCollarJetPerturbationCLM_ae (J : NativeCollarJet) :
    (nativeCollarJetPerturbationCLM a b c ha hb hc J : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => (∑ i : Fin 3,∑ j : Fin 3,a i j x*(J.2.2 i j : E → ℝ) x)+
        (∑ j : Fin 3,b j x*(J.2.1 j : E → ℝ) x)+c x*(J.1 : E → ℝ) x) := by
  let A := fun i j => nativeCollarScalarMulCLM (a i j) (ha i j) (J.2.2 i j)
  let B := fun j => nativeCollarScalarMulCLM (b j) (hb j) (J.2.1 j)
  let C := nativeCollarScalarMulCLM c hc J.1
  rw [nativeCollarJetPerturbationCLM_apply]
  filter_upwards [Lp.coeFn_add ((∑ i : Fin 3,∑ j : Fin 3,A i j)+(∑ j : Fin 3,B j)) C,
    Lp.coeFn_add (∑ i : Fin 3,∑ j : Fin 3,A i j) (∑ j : Fin 3,B j),collar_sum_ae (fun i => ∑ j : Fin 3,A i j),
    eventually_all.mpr (fun i => collar_sum_ae (A i)),collar_sum_ae B,
    eventually_all.mpr (fun i => eventually_all.mpr (fun j => nativeCollarScalarMulCLM_ae (a i j) (ha i j) (J.2.2 i j))),
    eventually_all.mpr (fun j => nativeCollarScalarMulCLM_ae (b j) (hb j) (J.2.1 j)),
    nativeCollarScalarMulCLM_ae c hc J.1] with x habc hab hsum hrow hsumB hA hB hC
  change (((∑ i : Fin 3,∑ j : Fin 3,A i j)+(∑ j : Fin 3,B j))+C : NativeCollarL2) x=_
  rw [habc]
  simp only [Pi.add_apply,hab,hsum,hrow,hsumB,hA,hB,hC,A,B,C]

#print axioms nativeCollarJetPerturbationCLM_apply
#print axioms nativeCollarJetPerturbationCLM_norm_le
#print axioms nativeCollarJetPerturbationCLM_ae
end Yamabe3.Analysis.SpherePolar
