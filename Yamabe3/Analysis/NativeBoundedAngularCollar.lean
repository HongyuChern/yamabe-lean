import Yamabe3.Analysis.NativeConjugatedCollarLift

/-! A bounded angular curve on the actual entrance time window gives
a quantitative physical collar L2 bound. The polar volume cost is kept. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay UniformElliptic

theorem native_bounded_angular_collar_norm {U:ℝ→AngularL2} (hU:Continuous U)
    {w:ℝ×S→ℝ} (hw:Measurable w)
    (hae:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](U t:S→ℝ))
    {B:ℝ} (hB:0≤B) (hb:∀t∈Icc (-(1/2:ℝ)) (1/2),‖U t‖≤B)
    (J:Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)) (hJ:(J:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift w) :
    ‖J‖≤Real.sqrt (Real.exp 1)*B := by
  have hm:=native_collar_lift_memLp hU hw hae
  have heq:J=hm.toLp (cylinderLift w):=Lp.ext (hJ.trans hm.coeFn_toLp.symm)
  have hmwide:=memLp_continuous_angular_lift hU hw hae (-(1/2:ℝ)) (1/2)
  have hsub:=setIntegral_mono_set (s:=nativePoissonEntranceCollar) hmwide.integrable_sq
    (Eventually.of_forall fun x=>sq_nonneg (cylinderLift w x))
    (Eventually.of_forall fun x hx=>nativeEntranceCollar_subset_shell hx)
  have hpol:=integral_cylinderLift_sq_shell_le hU hw hae (-(1/2:ℝ)) (1/2)
  have hi:(∫t:ℝ in Icc (-(1/2:ℝ)) (1/2),‖U t‖^2)≤B^2:=by
    have h:=setIntegral_mono_on (μ:=(volume:Measure ℝ)) (hU.norm.pow 2).integrableOn_Icc
      ((continuous_const:Continuous (fun _:ℝ=>B^2)).integrableOn_Icc) measurableSet_Icc
      (fun t ht=>(sq_le_sq₀ (norm_nonneg _) hB).mpr (hb t ht))
    norm_num [integral_const,Real.volume_Icc] at h ⊢
    exact h
  have hn:=native_norm_toLp_sq_eq_integral_sq hm
  rw [←heq] at hn
  have hh:‖J‖^2≤Real.exp 1*B^2:=by
    rw [hn]
    have h:=hsub.trans (hpol.trans (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le))
    norm_num only at h
    exact h
  have hs:(Real.sqrt (Real.exp 1)*B)^2=Real.exp 1*B^2:=by
    rw [mul_pow,Real.sq_sqrt (Real.exp_pos _).le]
  have hp:0≤Real.sqrt (Real.exp 1)*B:=mul_nonneg (Real.sqrt_nonneg _) hB
  nlinarith only [hh,hs,hp,norm_nonneg J]

#print axioms native_bounded_angular_collar_norm
end Yamabe3.Analysis.SpherePolar
