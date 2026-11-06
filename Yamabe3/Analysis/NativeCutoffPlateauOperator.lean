import Yamabe3.Analysis.NativeOuterCutoffActualOperator
import Yamabe3.Analysis.NativeFullShellEquation

/-! A cutoff that is genuinely one on a neighborhood of each retained
shell point leaves the full native operator's shell return unchanged.
The result is proved on C2 functions by operator germs, then extended to
the actual closed jet space by its established density and continuity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

 theorem nativeFullBCF_C2_actual_operator (g:RiemannianMetric 3 E) {r:ℝ} (hr:0<r)
    (V:ℝ→ᵇℝ) (u:nativeC2OffZero):
    ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) (nativeC2CollarJetLinear u):E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x=>nativeRescaledDelaunayJacobian g r (fun _=>0) 0 u.val x-
        g.pullbackVolumeDensity id (r • x)*nativeHalfEndPotentialCoefficient V x*u.val x):=by
  let J:nativeCollarJetClosure:=⟨nativeC2CollarJetLinear u,subset_closure ⟨u,rfl⟩⟩
  have hv:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u.val:=
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hweak:=nativeBCF_full_row_weak_ae g r V J
  have hc:=(nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g r (fun _=>0) 0 hv).trans
    (nativeWeakRescaledDelaunayJacobian_C2_ae g hr (fun _=>0) contDiff_const (fun _=>⟨le_rfl,by norm_num⟩) 0 u)
  filter_upwards [hweak,hc,hv] with x hx hc hv
  change ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) J.val:E→ℝ) x=_
  change ((nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val:NativeCollarL2):E→ℝ) x=_
  change nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g r (fun _=>0) 0 J.val.1 x=
    nativeRescaledDelaunayJacobian g r (fun _=>0) 0 u.val x at hc
  rw [hx,hc,hv]

 theorem nativeFullBCF_cutoff_plateau_shell_return
    (g:RiemannianMetric 3 E) {r:ℝ} (hr:0<r) (V:ℝ→ᵇℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈nativeSourceShell,χ=ᶠ[𝓝 x](fun _=>1)) (s:ℝ) (J:nativeCollarJetClosure):
    nativeFullShellSourceReturnCLM s
      ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) (nativeCollarCutoffCLM χ hχ J).val)=
    nativeFullShellSourceReturnCLM s ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) J.val):=by
  let A:=nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V
  let L:=nativeFullShellSourceReturnCLM s
  have hclosed:IsClosed {K:nativeCollarJetClosure|L (A (nativeCollarCutoffCLM χ hχ K).val)=L (A K.val)}:=
    isClosed_eq (L.comp (A.comp (nativeCollarJetClosure.subtypeL.comp (nativeCollarCutoffCLM χ hχ)))).continuous
      (L.comp (A.comp nativeCollarJetClosure.subtypeL)).continuous
  refine nativeC2CollarJetInclusion_dense.induction_on J hclosed ?_
  intro u
  have hcut:nativeCollarCutoffCLM χ hχ (nativeC2CollarJetInclusion u)=
      nativeC2CollarJetInclusion (nativeC2Cutoff χ hχ u):=by
    apply Subtype.ext
    exact nativeCollarCutoffRawCLM_C2 χ hχ u
  change L (A (nativeCollarCutoffCLM χ hχ (nativeC2CollarJetInclusion u)).val)=L (A (nativeC2CollarJetInclusion u).val)
  rw [hcut]
  apply nativeFullShellSourceReturn_eq_of_shell_ae
  have hμ:volume.restrict nativeSourceShell≤volume.restrict nativePoissonEntranceCollar:=
    Measure.restrict_mono nativeSourceShell_subset_collar le_rfl
  filter_upwards [ae_mono hμ (nativeFullBCF_C2_actual_operator g hr V (nativeC2Cutoff χ hχ u)),
    ae_mono hμ (nativeFullBCF_C2_actual_operator g hr V u),ae_restrict_mem nativeSourceShell_measurable] with x hcut hu hx
  change ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) (nativeC2CollarJetLinear (nativeC2Cutoff χ hχ u)):E→ℝ) x=_
  rw [hcut]
  change _=((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V) (nativeC2CollarJetLinear u):E→ℝ) x
  rw [hu]
  have he:(nativeC2Cutoff χ hχ u).val=ᶠ[𝓝 x]u.val:=by
    filter_upwards [h1 x hx] with y hy
    simp only [nativeC2Cutoff,hy,one_mul]
  simp only [nativeRescaledDelaunayJacobian]
  rw [principalSource_eq_of_eventuallyEq _ he,he.self_of_nhds]

#print axioms nativeFullBCF_C2_actual_operator
#print axioms nativeFullBCF_cutoff_plateau_shell_return
end Yamabe3.Analysis.SpherePolar
