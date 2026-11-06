import Yamabe3.Analysis.NativeAngularC2Spectral
import Yamabe3.Analysis.NativeL2HalfNormalTrace
import Yamabe3.Analysis.NativeTraceAngularCoordinates

/-! The actual C2 solution's literal sphere value and radial derivative
supply the required spectral trace classes. No independent boundary datum
or extra source integrability is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology Manifold ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2+1))) = 2+1) := ⟨by simp⟩

theorem nativeC2_sphere_value_regular (u : nativeC2OffZero) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 2 (fun θ : S => u.val (θ:E)) := by
  intro θ
  have hx : (θ:E)≠0 := by
    intro h
    have hn := norm_eq_of_mem_sphere θ
    rw [h,norm_zero] at hn
    norm_num at hn
  exact (u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)).contMDiffAt.comp θ
    contMDiff_coe_sphere.contMDiffAt

theorem nativeC2_sphere_normal_regular (u : nativeC2OffZero) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 (fun θ : S => fderiv ℝ u.val (θ:E) (θ:E)) := by
  intro θ
  have hx : (θ:E)≠0 := by
    intro h
    have hn := norm_eq_of_mem_sphere θ
    rw [h,norm_zero] at hn
    norm_num at hn
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u.val) (θ:E) :=
    (u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)).fderiv_right (by norm_num)
  exact (hd.contMDiffAt.comp θ contMDiff_coe_sphere.contMDiffAt).clm_apply contMDiff_coe_sphere.contMDiffAt

theorem nativeC2_value_trace_angular (u : nativeC2OffZero) :
    nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u))=
      continuousAngularL2 (fun θ : S => u.val (θ:E)) (nativeC2_sphere_value_regular u).continuous := by
  rw [(nativeCollarTraceCLM_agrees_C2 u).1]
  apply Lp.ext
  have h := (nativeTraceAngularCLM_ae (nativeC2ValueTraceLinear u)).trans (nativeC2ValueTraceLinear_ae u)
  have hc := continuousAngularL2_ae (fun θ : S => u.val (θ:E)) (nativeC2_sphere_value_regular u).continuous
  simpa only [Measure.restrict_univ] using h.trans hc.symm

theorem nativeC2_normal_trace_angular (u : nativeC2OffZero) :
    nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u))=
      continuousAngularL2 (fun θ : S => fderiv ℝ u.val (θ:E) (θ:E)) (nativeC2_sphere_normal_regular u).continuous := by
  rw [(nativeCollarTraceCLM_agrees_C2 u).2]
  apply Lp.ext
  have h := (nativeTraceAngularCLM_ae (nativeC2NormalTraceLinear u)).trans (nativeC2NormalTraceLinear_ae u)
  have hc := continuousAngularL2_ae (fun θ : S => fderiv ℝ u.val (θ:E) (θ:E)) (nativeC2_sphere_normal_regular u).continuous
  simpa only [Measure.restrict_univ] using h.trans hc.symm

theorem nativeC2_actual_trace_spectral (u : nativeC2OffZero) :
    NativeAngularSpectralRegular (3/2)
      (nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u))) ∧
    NativeAngularSpectralRegular (1/2)
      (nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u))) := by
  rw [nativeC2_value_trace_angular,nativeC2_normal_trace_angular]
  exact ⟨(angular_C2_three_halves_trace _ (nativeC2_sphere_value_regular u)).1,
    (angular_C1_half_trace _ (nativeC2_sphere_normal_regular u)).1⟩

#print axioms nativeC2_sphere_value_regular
#print axioms nativeC2_sphere_normal_regular
#print axioms nativeC2_value_trace_angular
#print axioms nativeC2_normal_trace_angular
#print axioms nativeC2_actual_trace_spectral
end Yamabe3.Analysis.SpherePolar
