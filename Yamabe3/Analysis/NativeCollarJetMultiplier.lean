import Yamabe3.Analysis.DensityCutoffCommutatorCLM

/-! Multiplication by one fixed smooth cutoff acts on the actual strong
collar jet closure. Every first and second product term is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Poincare.Analysis.Elliptic.Iteration

private theorem multiplier_partial_smooth {f:E→ℝ} (hf:ContDiff ℝ ∞ f) (i:Fin 3) :
    ContDiff ℝ ∞ (partialDeriv i f) :=
  (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)

def nativeCollarCutoffFirstCLM (j:Fin 3) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  (nativeCollarScalarMulCLM (partialDeriv j χ) (multiplier_partial_smooth hχ j).continuous).comp
    nativeCollarJetValueCLM+
  (nativeCollarScalarMulCLM χ hχ.continuous).comp (nativeCollarJetFirstCLM j)

def nativeCollarCutoffSecondCLM (i j:Fin 3) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  ((nativeCollarScalarMulCLM (partialDeriv i (partialDeriv j χ))
    (multiplier_partial_smooth (multiplier_partial_smooth hχ j) i).continuous).comp nativeCollarJetValueCLM+
   (nativeCollarScalarMulCLM (partialDeriv j χ) (multiplier_partial_smooth hχ j).continuous).comp
      (nativeCollarJetFirstCLM i))+
  ((nativeCollarScalarMulCLM (partialDeriv i χ) (multiplier_partial_smooth hχ i).continuous).comp
      (nativeCollarJetFirstCLM j)+
   (nativeCollarScalarMulCLM χ hχ.continuous).comp (nativeCollarJetSecondCLM i j))

def nativeCollarCutoffRawCLM : NativeCollarJet →L[ℝ] NativeCollarJet :=
  ((nativeCollarScalarMulCLM χ hχ.continuous).comp nativeCollarJetValueCLM).prod
    ((ContinuousLinearMap.pi (nativeCollarCutoffFirstCLM χ hχ)).prod
      (ContinuousLinearMap.pi fun i=>ContinuousLinearMap.pi (nativeCollarCutoffSecondCLM χ hχ i)))

private theorem multiplier_add_ae {U V:NativeCollarL2} {u v:E→ℝ}
    (hu:(U:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u)
    (hv:(V:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] v) :
    ((U+V:NativeCollarL2):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] (fun x=>u x+v x) :=
  (Lp.coeFn_add U V).trans (hu.add hv)

private theorem multiplier_mul_ae (q:E→ℝ) (hq:Continuous q) {U:NativeCollarL2} {u:E→ℝ}
    (hu:(U:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u) :
    (nativeCollarScalarMulCLM q hq U:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] (fun x=>q x*u x) :=
  (nativeCollarScalarMulCLM_ae q hq U).trans ((EventuallyEq.refl _ _).mul hu)

def nativeC2Cutoff (u:nativeC2OffZero) : nativeC2OffZero :=
  ⟨fun x=>χ x*u.val x,(hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn.mul u.property⟩

theorem nativeCollarCutoffRawCLM_C2 (u:nativeC2OffZero) :
    nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u)=
      nativeC2CollarJetLinear (nativeC2Cutoff χ hχ u) := by
  have hv:(nativeC2CollarValue u.property:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u.val :=
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hp (j:Fin 3):(nativeC2CollarFirst u.property j:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      partialDeriv j u.val := (nativeC2Collar_memLp u.property).2.1 j |>.coeFn_toLp
  have hpp (i j:Fin 3):(nativeC2CollarSecond u.property i j:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      partialDeriv i (partialDeriv j u.val) := (nativeC2Collar_memLp u.property).2.2 i j |>.coeFn_toLp
  apply Prod.ext
  · apply Lp.ext
    exact (multiplier_mul_ae χ hχ.continuous hv).trans
      ((nativeC2Collar_memLp (nativeC2Cutoff χ hχ u).property).1.coeFn_toLp).symm
  · apply Prod.ext
    · funext j
      apply Lp.ext
      have hr:=multiplier_add_ae
        (multiplier_mul_ae (partialDeriv j χ) (multiplier_partial_smooth hχ j).continuous hv)
        (multiplier_mul_ae χ hχ.continuous (hp j))
      filter_upwards [hr,(nativeC2Collar_memLp (nativeC2Cutoff χ hχ u).property).2.1 j |>.coeFn_toLp,
        ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hy hO
      change (nativeCollarCutoffFirstCLM χ hχ j (nativeC2CollarJetLinear u):E→ℝ) x=_
      change (nativeCollarCutoffFirstCLM χ hχ j (nativeC2CollarJetLinear u):E→ℝ) x=_ at hx
      change ((nativeC2CollarJetLinear (nativeC2Cutoff χ hχ u)).2.1 j:E→ℝ) x=_ at hy
      rw [hx,hy]
      exact (partialDeriv_mul_at (hχ.differentiable (by simp) x)
        ((u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds
          (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hO)))).differentiableAt (by norm_num)) j).symm
    · funext i j
      apply Lp.ext
      have hr:=multiplier_add_ae
        (multiplier_add_ae
          (multiplier_mul_ae (partialDeriv i (partialDeriv j χ))
            (multiplier_partial_smooth (multiplier_partial_smooth hχ j) i).continuous hv)
          (multiplier_mul_ae (partialDeriv j χ) (multiplier_partial_smooth hχ j).continuous (hp i)))
        (multiplier_add_ae
          (multiplier_mul_ae (partialDeriv i χ) (multiplier_partial_smooth hχ i).continuous (hp j))
          (multiplier_mul_ae χ hχ.continuous (hpp i j)))
      filter_upwards [hr,(nativeC2Collar_memLp (nativeC2Cutoff χ hχ u).property).2.2 i j |>.coeFn_toLp,
        ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hy hO
      change (nativeCollarCutoffSecondCLM χ hχ i j (nativeC2CollarJetLinear u):E→ℝ) x=_
      change (nativeCollarCutoffSecondCLM χ hχ i j (nativeC2CollarJetLinear u):E→ℝ) x=_ at hx
      change ((nativeC2CollarJetLinear (nativeC2Cutoff χ hχ u)).2.2 i j:E→ℝ) x=_ at hy
      rw [hx,hy]
      have he:=partialDeriv_second_mul_on isClosed_singleton.isOpen_compl
        (hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn u.property
        (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hO)) i j
      change _=partialDeriv i (partialDeriv j (fun y=>χ y*u.val y)) x
      rw [he]
      ring

theorem nativeCollarCutoffRawCLM_mem (J:nativeCollarJetClosure) :
    nativeCollarCutoffRawCLM χ hχ J.val∈nativeCollarJetClosure := by
  have hc:=nativeC2CollarJetLinear.range.isClosed_topologicalClosure.preimage
    ((nativeCollarCutoffRawCLM χ hχ).comp nativeCollarJetClosure.subtypeL).continuous
  refine nativeC2CollarJetInclusion_dense.induction_on J hc ?_
  intro u
  change nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u)∈nativeCollarJetClosure
  rw [nativeCollarCutoffRawCLM_C2]
  exact nativeC2CollarJetLinear.range.le_topologicalClosure ⟨nativeC2Cutoff χ hχ u,rfl⟩

def nativeCollarCutoffCLM : nativeCollarJetClosure →L[ℝ] nativeCollarJetClosure :=
  ((nativeCollarCutoffRawCLM χ hχ).comp nativeCollarJetClosure.subtypeL).codRestrict
    nativeCollarJetClosure (nativeCollarCutoffRawCLM_mem χ hχ)

theorem nativeCollarCutoffCLM_value_ae (J:nativeCollarJetClosure) :
    ((nativeCollarCutoffCLM χ hχ J).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>χ x*(J.val.1:E→ℝ) x) :=
  nativeCollarScalarMulCLM_ae χ hχ.continuous J.val.1

#print axioms nativeCollarCutoffRawCLM_C2
#print axioms nativeCollarCutoffRawCLM_mem
#print axioms nativeCollarCutoffCLM_value_ae
end Yamabe3.Analysis.SpherePolar
