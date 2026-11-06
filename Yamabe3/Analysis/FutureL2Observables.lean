import Yamabe3.Analysis.LowL2WeakEquation

/-! Continuous linear observables commute with the actual L2 future
integral. This preserves the genuine low angular source subspace. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

 theorem futureL2Resolvent_observable
    {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J]
    {k : ℝ} (hk : 0<k) (L : H →L[ℝ] J) (F : Lp H 2 (volume : Measure ℝ)) :
    L.compLp (futureL2ResolventCLM k hk F)=futureL2ResolventCLM k hk (L.compLp F) := by
  apply Lp.ext
  have hR := futureL2Resolvent_coe_ae hk (L.compLp F)
  rw [futureL2Convolution_congr_ae k (L.coeFn_compLp F)] at hR
  filter_upwards [L.coeFn_compLp (futureL2ResolventCLM k hk F),
    futureL2Resolvent_coe_ae hk F,hR,futureL2Convolution_integrable_Lp hk F] with t hL hF hR hi
  change (futureL2ResolventCLM k hk F : ℝ → H) t=_ at hF
  change (futureL2ResolventCLM k hk (L.compLp F) : ℝ → J) t=_ at hR
  rw [hL,hF,hR]
  change L (∫ s : ℝ,futureL2Kernel k (t-s) • F s)=∫ s : ℝ,futureL2Kernel k (t-s) • L (F s)
  rw [←L.integral_comp_comm hi]
  simp only [map_smul]

 theorem doubleFutureL2_observable
    {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace J]
    {k : ℝ} (hk : 0<k) (L : H →L[ℝ] J) (F : Lp H 2 (volume : Measure ℝ)) :
    L.compLp (doubleFutureL2CLM k hk F)=doubleFutureL2CLM k hk (L.compLp F) := by
  change L.compLp (futureL2ResolventCLM k hk (futureL2ResolventCLM k hk F))=_
  rw [futureL2Resolvent_observable,futureL2Resolvent_observable]
  rfl

 theorem lowL2FutureInverse_observable_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) (L : H →L[ℝ] ℝ)
    (hF : ∀ᵐ t : ℝ,L (F t)=0) (hA0 : ∀ t x,L (A t x)=0) :
    L.compLp (lowL2FutureInverseCLM A hA F)=0 := by
  let U := lowL2FutureInverseCLM A hA F
  have hLF : L.compLp F=0 := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLp F,hF,Lp.coeFn_zero ℝ 2 volume] with t ht hft hz
    exact ht.trans (hft.trans hz.symm)
  have hLU : L.compLp (l2BoundedOperatorActionCLM A U)=0 := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLp (l2BoundedOperatorActionCLM A U),l2BoundedOperatorAction_ae A U,
      Lp.coeFn_zero ℝ 2 volume] with t ht hU hz
    change (l2BoundedOperatorActionCLM A U : ℝ → H) t=_ at hU
    rw [ht,hU,hA0,hz]
    rfl
  have hf := congrArg (fun Z : Lp H 2 (volume : Measure ℝ) => L.compLp Z) (lowL2FutureInverse_fixed A hA F)
  rw [doubleFutureL2_observable] at hf
  change doubleFutureL2CLM 2 (by norm_num) ((L.compLpL 2 volume) (F+l2BoundedOperatorActionCLM A U))=L.compLp U at hf
  change (L.compLpL 2 volume) F=0 at hLF
  change (L.compLpL 2 volume) (l2BoundedOperatorActionCLM A U)=0 at hLU
  rw [map_add,hLF,hLU,add_zero,map_zero] at hf
  exact hf.symm

 theorem nativeLowL2FutureInverse_high_zero (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0≤v t ∧ v t≤1) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (i : SphereSpectrum.AngularIndex) (hi : 6≤SphereSpectrum.angularEigenvalue i)
    (hF : ∀ᵐ t : ℝ,F t i=0) :
    ∀ᵐ t : ℝ,nativeLowL2FutureInverseCLM v hv hb F t i=0 := by
  let L := lp.evalCLM ℝ (fun _ : SphereSpectrum.AngularIndex => ℝ) 2 i
  have hz := lowL2FutureInverse_observable_zero (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) F L hF (fun t x => by
      change lowAngularCoefficient v t i*x i=0
      rw [lowAngularCoefficient,if_neg (not_lt.mpr hi),zero_mul])
  have he := L.coeFn_compLp (nativeLowL2FutureInverseCLM v hv hb F)
  change L.compLp (nativeLowL2FutureInverseCLM v hv hb F)=0 at hz
  rw [hz] at he
  filter_upwards [he,Lp.coeFn_zero ℝ 2 volume] with t ht hz
  exact ht.symm.trans hz

#print axioms futureL2Resolvent_observable
#print axioms doubleFutureL2_observable
#print axioms lowL2FutureInverse_observable_zero
#print axioms nativeLowL2FutureInverse_high_zero
end Yamabe3.Analysis.Delaunay
