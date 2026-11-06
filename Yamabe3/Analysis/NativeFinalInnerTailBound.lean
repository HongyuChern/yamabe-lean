import Yamabe3.Analysis.NativeOriginalTailH4
import Yamabe3.Analysis.NativeH4MatchedAllScale
import Yamabe3.Analysis.NativeTwoSidedAllScale

/-! Uniform actual H4 tail bound from the SAME source, actual jets and
local PDE. Constants precede the final feedback source and physical scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem exists_nativeFinal_inner_tail_H4_bound
    (gE:RiemannianMetric 3 E) (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    {κ:ℝ} (hκ0:0≤ κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤ κ)
    (τ:ℝ) (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (CSource:ℝ) (hCS:0≤ CSource):
    let P:=p.nativeHighPotential hκ0 hκ1
    let v:=fun t=>p.orbit (t+p.phase)
    let hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
    let hb:∀t,0≤ v t ∧ v t≤ 1:=fun t=>p.bounded (t+p.phase)
    ∃d:ℝ,∃H:ℝ≥0∞,0<d ∧ H≠⊤ ∧ ∀a:ℝ,0≤ a→a<d→
      ∀(f:HalfEndPhysicalH2SourceGraph)(Y:NativeTwoSidedSource)(u:E→ℝ),
        ‖Y‖≤ CSource*‖f‖→MemWkpLocally 4 u (ball (0:E) 1\{0})→
        (∀U:Set E,IsOpen U→IsCompact (closure U)→closure U⊆ball (0:E) 1\{0}→
          nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
            =ᵐ[volume.restrict U]fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)→
        (∀i:HalfEndPhysicalSliceIndex,
          ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
            nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val Y).val.1:E→ℝ)
            =ᵐ[volume.restrict nativePoissonEntranceCollar]
              fun x=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • x))→
        ∀s:ℝ,4≤ s→MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
          iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤ H*ENNReal.ofReal ‖f‖:=by
  dsimp only
  let P:=p.nativeHighPotential hκ0 hκ1
  let v:=fun t=>p.orbit (t+p.phase)
  let hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  let hb:∀t,0≤ v t ∧ v t≤ 1:=fun t=>p.bounded (t+p.phase)
  obtain ⟨d,hd,H,hH,htail⟩:=exists_native_original_tail_H4_bound gE hB hρ
  obtain ⟨D₀,hD₀,h₀⟩:=exists_nativeH4MatchedScale_bound (fullBubbleHighPotential (-τ)) P hp
  obtain ⟨D₁,hD₁,h₁⟩:=exists_nativeTwoSidedAllScale_bound P hp v hv hb τ
  let B:=D₀*‖T₀‖+D₁*CSource
  have hBn:0≤ B:=by dsimp only [B];positivity
  refine ⟨d,H*(ENNReal.ofReal B+1),hd,by finiteness,fun a ha had f Y u hY hu he hjet=>?_⟩
  apply htail a ha had p.orbit p.smooth
    (fun t=>⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩) p.ode p.phase f u hu he B hBn
  intro s hs
  have hsidx:-Real.log 2≤ s:=by have hlog:=Real.log_nonneg (by norm_num:(1:ℝ)≤ 2);linarith
  let i:HalfEndPhysicalSliceIndex:=⟨s,hsidx⟩
  refine ⟨nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
    nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y,hjet i,?_⟩
  have h0:‖nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)‖≤ D₀*(‖T₀‖*‖f‖):=
    ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i).le_of_opNorm_le (h₀ i) _).trans
      (mul_le_mul_of_nonneg_left (T₀.le_opNorm f) hD₀.le)
  have h1:‖nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y‖≤ D₁*(CSource*‖f‖):=
    ((nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s).le_of_opNorm_le (h₁ s) Y).trans
      (mul_le_mul_of_nonneg_left hY hD₁.le)
  exact (norm_add_le _ _).trans ((add_le_add h0 h1).trans_eq (by dsimp only [B];ring))

#print axioms exists_nativeFinal_inner_tail_H4_bound
end Yamabe3.Analysis.SpherePolar
