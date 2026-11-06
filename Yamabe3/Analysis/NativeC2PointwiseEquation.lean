import Yamabe3.Analysis.NativeLocalC2CauchyGluing
import Yamabe3.Analysis.NativeOriginalManifoldSourceSolver

/-! Continuous actual C2 fields and actual source-graph representatives
upgrade the local almost-everywhere equation to a pointwise equation.
No exceptional volume set is restricted to a boundary sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay EuclideanSphereTrace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E3) 1 \ {(0:E3)}
local notation "P" => ({(0:E3)}ᶜ:Set E3)

theorem continuousOn_native_laplacian_C2 (g:RiemannianMetric 3 E3)
    {U:Set E3} (hU:IsOpen U) {f:E3→ℝ} (hf:ContDiffOn ℝ 2 f U):
    ContinuousOn (g.leviCivitaData.laplacian f) U:=by
  intro x hx
  obtain ⟨F,hF,_,hFg⟩:=exists_compact_C2_extension_near_compact hU
    (isCompact_singleton (x:=x)) (singleton_subset_iff.mpr hx) hf
  have he:=hFg x (mem_singleton x)
  have hl:g.leviCivitaData.laplacian F=ᶠ[𝓝 x]g.leviCivitaData.laplacian f:=by
    filter_upwards [he.eventuallyEq_nhds] with y hy
    exact g.leviCivitaData.laplacian_eq_of_eventuallyEq hy
  exact ((continuous_native_laplacian_C2 g hF).continuousAt.congr_of_eventuallyEq hl.symm).continuousWithinAt

theorem continuousOn_halfEndEuclideanPhysicalSource (f:HalfEndSourceValue):
    ContinuousOn (halfEndEuclideanPhysicalSource f) O:=by
  have hsub:ContinuousOn (halfEndSourceExtension f) O:=by
    rw [continuousOn_iff_continuous_restrict]
    let k:↥(O:Set E3)→HalfEndSourceEntrance:=fun x=>⟨x,⟨x.2.2,by
      have hn:‖(x:E3)‖<1:=by simpa only [mem_ball,dist_zero_right] using x.2.1
      linarith⟩⟩
    have hk:Continuous k:=continuous_subtype_val.subtype_mk _
    have he:(fun x:↥(O:Set E3)=>halfEndSourceExtension f x)=fun x:↥(O:Set E3)=>f (k x):=by
      funext x
      exact halfEndSourceExtension_of_mem f (k x).2
    change Continuous (fun x:↥(O:Set E3)=>halfEndSourceExtension f x)
    rw [he]
    exact f.continuous.comp hk
  have hr:ContinuousOn (fun x:E3=>radialScale ‖x‖) O:=by
    intro x hx
    exact ((radialScale_hasDerivAt (norm_pos_iff.mpr hx.2)).continuousAt.comp
      (f:=fun y:E3=>‖y‖) continuous_norm.continuousAt).continuousWithinAt
  exact (continuousOn_const.mul hr).mul hsub

theorem eqOn_of_precompact_ae {U:Set E3} (hU:IsOpen U) {f h:E3→ℝ}
    (hf:ContinuousOn f U) (hh:ContinuousOn h U)
    (heq:∀V:Set E3,IsOpen V→IsCompact (closure V)→closure V⊆U→f =ᵐ[volume.restrict V]h):
    EqOn f h U:=by
  intro x hx
  obtain ⟨V,hV,hxV,hVU,hVc⟩:=exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=x)) hU (singleton_subset_iff.mpr hx)
  have hsub:V⊆U:=subset_closure.trans hVU
  exact Measure.eqOn_open_of_ae_eq (heq V hV hVc hVU) hV (hf.mono hsub) (hh.mono hsub) (hxV (mem_singleton x))

def nativeScaledJacobianExpression (g:RiemannianMetric 3 E3) (ε:ℝ)
    (v:ℝ→ℝ) (τ:ℝ) (F:E3→ℝ) (x:E3):ℝ:=
  ε^2*g.pullbackVolumeDensity id (ε • x)*
    (-8*g.leviCivitaData.laplacian (fun y=>F (ε⁻¹ • y)) (ε • x)+
      (g.leviCivitaData.scalarCurvature (ε • x)-
        30*radialProfile v (τ+Real.log ε) ‖ε • x‖^4)*F x)

theorem continuousOn_nativeScaledJacobianExpression_C2
    (g:RiemannianMetric 3 E3) {ε:ℝ} (hε:0<ε)
    {v:ℝ→ℝ} (hv:ContDiff ℝ ∞ v) (τ:ℝ)
    {F:E3→ℝ} (hF:ContDiffOn ℝ 2 F P):
    ContinuousOn (nativeScaledJacobianExpression g ε v τ F) P:=by
  have hP:IsOpen P:=isClosed_singleton.isOpen_compl
  have hmap:MapsTo (fun y:E3=>ε • y) P P:=by
    intro y hy
    exact smul_ne_zero hε.ne' hy
  have hi:MapsTo (fun y:E3=>ε⁻¹ • y) P P:=by
    intro y hy
    exact smul_ne_zero (inv_ne_zero hε.ne') hy
  have hw:ContDiffOn ℝ 2 (fun y:E3=>F (ε⁻¹ • y)) P:=
    hF.comp (contDiff_id.const_smul ε⁻¹).contDiffOn hi
  have hl:ContinuousOn (fun x:E3=>g.leviCivitaData.laplacian (fun y=>F (ε⁻¹ • y)) (ε • x)) P:=
    (continuousOn_native_laplacian_C2 g hP hw).comp (continuous_id.const_smul ε).continuousOn hmap
  have hrho:Continuous (fun x:E3=>g.pullbackVolumeDensity id (ε • x)):=
    (GreenParametrix.native_density_smooth_positive g).1.continuous.comp (continuous_id.const_smul ε)
  have hsc:Continuous (fun x:E3=>g.leviCivitaData.scalarCurvature (ε • x)):=
    g.leviCivitaData.continuous_scalarCurvature.comp (continuous_id.const_smul ε)
  have hr:ContinuousOn (fun x:E3=>radialProfile v (τ+Real.log ε) ‖ε • x‖) P:=
    (radialProfile_contDiffOn hv _).continuousOn.comp
      (continuous_norm.comp (continuous_id.const_smul ε)).continuousOn
      (fun x hx=>norm_pos_iff.mpr (hmap hx))
  exact (continuousOn_const.mul hrho.continuousOn).mul
    ((continuousOn_const.mul hl).add ((hsc.continuousOn.sub (continuousOn_const.mul (hr.pow 4))).mul hF.continuousOn))

theorem native_scaled_source_pointwise
    (g:RiemannianMetric 3 E3) {ε:ℝ} (hε:0<ε)
    {v:ℝ→ℝ} (hv:ContDiff ℝ ∞ v) (τ:ℝ)
    {F:E3→ℝ} (hF:ContDiffOn ℝ 2 F P) (f:HalfEndSourceValue)
    (heq:∀U:Set E3,IsOpen U→IsCompact (closure U)→closure U⊆O→
      nativeScaledJacobianExpression g ε v τ F =ᵐ[volume.restrict U]halfEndEuclideanPhysicalSource f):
    EqOn (nativeScaledJacobianExpression g ε v τ F) (halfEndEuclideanPhysicalSource f) O:=by
  apply eqOn_of_precompact_ae (isOpen_ball.sdiff isClosed_singleton)
    ((continuousOn_nativeScaledJacobianExpression_C2 g hε hv τ hF).mono (fun x hx=>hx.2))
    (continuousOn_halfEndEuclideanPhysicalSource f) heq

#print axioms continuousOn_native_laplacian_C2
#print axioms continuousOn_halfEndEuclideanPhysicalSource
#print axioms native_scaled_source_pointwise
end Yamabe3.Analysis.UniformElliptic
