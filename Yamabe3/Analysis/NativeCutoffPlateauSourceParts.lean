import Yamabe3.Analysis.NativeCutoffPlateauOperator

/-! On the genuine cutoff plateau, BOTH flat and geometric source
returns are separately unchanged. The commutator is actually zero there;
this is proved from the cutoff derivatives, not asserted as a source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay Poincare.Analysis.Elliptic.Iteration

private theorem plateau_partial_germ {χ:E→ℝ} {x:E} {c:ℝ}
    (h:χ=ᶠ[𝓝 x](fun _=>c)) (i:Fin 3):partialDeriv i χ=ᶠ[𝓝 x](fun _=>0):=by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  simp only [partialDeriv,hy,fderiv_const_apply,zero_apply]

 theorem nativeCutoffPlateau_commutator_return_zero
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈nativeSourceShell,χ=ᶠ[𝓝 x](fun _=>1)) (s:ℝ) (J:nativeCollarJetClosure):
    nativeFullShellSourceReturnCLM s (nativeCollarCutoffCommutatorCLM χ hχ J.val)=0:=by
  have he:((nativeCollarCutoffCommutatorCLM χ hχ J.val):E→ℝ)=ᵐ[volume.restrict nativeSourceShell]
      ((0:NativeCollarL2):E→ℝ):=by
    have hμ:volume.restrict nativeSourceShell≤volume.restrict nativePoissonEntranceCollar:=
      Measure.restrict_mono nativeSourceShell_subset_collar le_rfl
    filter_upwards [ae_mono hμ (nativeCollarCutoffCommutator_ae χ hχ J),
      ae_mono hμ (Lp.coeFn_zero ℝ 2 (volume.restrict nativePoissonEntranceCollar)),
      ae_restrict_mem nativeSourceShell_measurable] with x hx hz hxS
    have hp(i:Fin 3):partialDeriv i χ x=0:=
      (plateau_partial_germ (h1 x hxS) i).self_of_nhds
    have hpp(i:Fin 3):partialDeriv i (partialDeriv i χ) x=0:=
      (plateau_partial_germ (plateau_partial_germ (h1 x hxS) i) i).self_of_nhds
    rw [hx,hz]
    simp only [weakCutoffCommutator,hp,hpp,zero_mul,mul_zero,add_zero,Finset.sum_const_zero,neg_zero,Pi.zero_apply]
  exact (nativeFullShellSourceReturn_eq_of_shell_ae s _ 0 he).trans (map_zero _)

 theorem nativeCutoffPlateau_scalar_return
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈nativeSourceShell,χ=ᶠ[𝓝 x](fun _=>1)) (s:ℝ) (U:NativeCollarL2):
    nativeFullShellSourceReturnCLM s (nativeCollarScalarMulCLM χ hχ.continuous U)=
      nativeFullShellSourceReturnCLM s U:=by
  apply nativeFullShellSourceReturn_eq_of_shell_ae
  have hμ:volume.restrict nativeSourceShell≤volume.restrict nativePoissonEntranceCollar:=
    Measure.restrict_mono nativeSourceShell_subset_collar le_rfl
  filter_upwards [ae_mono hμ (nativeCollarScalarMulCLM_ae χ hχ.continuous U),
    ae_restrict_mem nativeSourceShell_measurable] with x hx hxS
  rw [hx,(h1 x hxS).self_of_nhds,one_mul]

 theorem nativeFlatCutoffPlateau_shell_return
    (V:ℝ→ᵇℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈nativeSourceShell,χ=ᶠ[𝓝 x](fun _=>1)) (s:ℝ) (J:nativeCollarJetClosure):
    nativeFullShellSourceReturnCLM s (nativeFlatCollarJetCLM V (nativeCollarCutoffCLM χ hχ J).val)=
      nativeFullShellSourceReturnCLM s (nativeFlatCollarJetCLM V J.val):=by
  rw [nativeFlatCollar_cutoff_exact_source,map_add,nativeCutoffPlateau_scalar_return χ hχ h1 s,
    nativeCutoffPlateau_commutator_return_zero χ hχ h1 s,add_zero]

 theorem nativeGeometricCutoffPlateau_shell_return
    (g:RiemannianMetric 3 E) {r:ℝ} (hr:0<r) (V:ℝ→ᵇℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈nativeSourceShell,χ=ᶠ[𝓝 x](fun _=>1)) (s:ℝ) (J:nativeCollarJetClosure):
    nativeFullShellSourceReturnCLM s (nativeBCFCollarErrorCLM g r V (nativeCollarCutoffCLM χ hχ J).val)=
      nativeFullShellSourceReturnCLM s (nativeBCFCollarErrorCLM g r V J.val):=by
  have hh:=nativeFullBCF_cutoff_plateau_shell_return g hr V χ hχ h1 s J
  simp only [ContinuousLinearMap.add_apply,map_add] at hh
  rw [nativeFlatCutoffPlateau_shell_return V χ hχ h1 s J] at hh
  exact add_left_cancel hh

#print axioms nativeCutoffPlateau_commutator_return_zero
#print axioms nativeCutoffPlateau_scalar_return
#print axioms nativeFlatCutoffPlateau_shell_return
#print axioms nativeGeometricCutoffPlateau_shell_return
end Yamabe3.Analysis.SpherePolar
