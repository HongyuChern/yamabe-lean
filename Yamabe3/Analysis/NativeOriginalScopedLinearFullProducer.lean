import Yamabe3.Analysis.NativeSmoothOriginalEntranceAssembly
import Yamabe3.Analysis.NativeOriginalScopedLinearProducer
import Yamabe3.Analysis.NativeFinalInnerTailBound
import Yamabe3.Analysis.NativeSmoothOriginalInnerTailAssembly
import Yamabe3.Analysis.NativeOriginalScopedLinearClosure
import Yamabe3.Analysis.NativeSmoothOriginalBoundedGlobalProducer
import Yamabe3.Analysis.NativeOrderedEnergyTraceProducer
import Yamabe3.Analysis.NativeFinalFeedbackSourceMap
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
import Yamabe3.Analysis.NativeSmoothPotentialUniformGap
import Yamabe3.Analysis.NativeSmoothPotentialFeedback
import Yamabe3.Analysis.NativeOrderedEnergyProducer
import Yamabe3.Analysis.NativeOrderedEnergySourceFeedback
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization

/-! Actual original-source native linear closure for one retained chart and
one Delaunay phase: same completed field, genuine smooth exterior potential,
actual conormal cancellation, uniform source/tail bounds and an actual
one-sided H4 entrance extension for the SAME representative.
Entrance constants here are explicitly pointwise in the physical scale;
this declaration does not claim the paper's full multipuncture Holder inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def signedOriginalNormed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] signedOriginalNormed


private instance producer32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
theorem exists_nativeOriginal_scoped_linear_full_closure
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ) {τ:ℝ} (ht:0 < τ) :
    let P:=p.nativeHighPotential hκ0 hκ1
    let v:=fun t=>p.orbit (t+p.phase)
    let hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
    let hb:∀t,0 ≤ v t ∧ v t ≤ 1:=fun t=>p.bounded (t+p.phase)
    ∃(cTail:ℝ) (m n:ℕ) (b S δ CR CM C N CI Ccore Cbase CY CSource:ℝ) (χin χout χSm:E→ℝ)
      (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout) (hχSm:ContDiff ℝ ∞ χSm) (hcSm:HasCompactSupport χSm) (s:ℝ)
      (O:Set E) (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
      (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O) (Htail:ℝ≥0∞),
      Htail≠⊤ ∧
      0<N ∧ 0≤CI ∧ 0≤Ccore ∧ 0≤Cbase ∧ 0≤CY ∧ 0≤CSource ∧ NativeEnergyReceivingTailSolver g e (closedBall (0:E) R₀) τ 64 cTail N ∧
      (∀x:E,0≤χSm x ∧ χSm x≤1) ∧ (∀x∈closedBall (0:E) (Real.exp s),χSm x=1) ∧
      tsupport χSm⊆ball (0:E) (2*Real.exp s) ∧ 64≤Real.exp s ∧
      Real.log 128 ≤ cTail ∧ Real.log 64+1 < (m:ℝ)/2 ∧ S ≤ -τ-3 ∧
      0 < δ ∧ 0 ≤ C ∧ NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀ ∧
      ∀a:ℝ,∀ha:0 < a,a ≤ δ → ∃ha1:a ≤ 1,
        ∃W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
          (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
          (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
          (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1,
        ‖W.I‖≤CI*Real.exp (-Real.log a/2) ∧
        (∀R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)),
          ‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val‖≤Ccore*‖R‖) ∧
        ∃(Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
          (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ),
          NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase ∧
          (∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
            (isCompact_closedBall (0:E) R₀) hsource (euclideanL2DilationCLM ha ha1 (toL2 Deuc O (L₀ f)))) ∧
          ‖nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase‖ ≤ C*Real.sqrt a ∧
          ∃hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χSm),
          ∃q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure,
            (q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
              nativeScaledSmoothBubblePotential e τ a χSm y) ∧
          ∃T:(H1Zero g.leviCivitaData univ) →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)),
            ‖T‖≤N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖) ∧
            ‖T‖≤1/2 ∧
            (∀z:H1Zero g.leviCivitaData univ,∀η:H1Zero g.leviCivitaData univ,
              closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
                ∫y,(nativeCriticalPotentialReactionCLM g hY q z y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀)
                  (fullBubbleScaledTail τ cTail (Real.log a)) y*toL2 g.leviCivitaData univ (T z).val y))*
                  toL2 g.leviCivitaData univ η y ∂g.volumeMeasure) ∧
          ∃JSm:H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ,
            ‖JSm‖≤2 ∧ (∀z:H1Zero g.leviCivitaData univ,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z))) ∧
            ‖JSm.comp (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase)‖≤(2*C)*Real.sqrt a ∧
            ‖nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm‖≤CSource ∧
            NativeOriginalScopedLinearClosure hκ0 hκ1 p hp W hcoeff T₀ Q₀ Rbase χSm hSm T JSm ∧
            let Y:=nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm
            let Ji:=fun f=>nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
              nativeTwoSidedInteriorJetCLM P hp v hv hb τ (Y f).val
            let Ko:=fun f=>nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
              nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (Y f).val 0
            ∃(Nentry:SpherePolar.S→Set E)(Lentry:SpherePolar.S→(E→ℝ)→ₗ[ℝ](E→ℝ))(Centry:SpherePolar.S→ℝ≥0∞),
              (∀θ:SpherePolar.S,(θ:E)∈Nentry θ ∧ IsOpen (Nentry θ) ∧ IsCompact (closure (Nentry θ)) ∧
                closure (Nentry θ)⊆nativePoissonEntranceCollar ∧ Centry θ≠⊤) ∧
              ∀f:HalfEndPhysicalH2SourceGraph,
                let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
                ∃u:E→ℝ,Measurable u ∧
                  (toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict
                    (e '' euclideanDilatedDomain a (ball (0:E) 1))]coordinateExtension e (fun x:E=>u (a⁻¹ • x)) ∧
                  MemWkpLocally 4 u (ball (0:E) 1\{0}) ∧
                  (∀U:Set E,IsOpen U→IsCompact (closure U)→closure U⊆ball (0:E) 1\{0}→
                    nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
                      =ᵐ[volume.restrict U]fun y=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8) ∧
                  (∀s:ℝ,4≤ s→MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
                    iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤Htail*ENNReal.ofReal ‖f‖) ∧
                  ∀θ:SpherePolar.S,
                    MemWkp 4 2 (Lentry θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)) (Nentry θ) ∧
                    iteratedWeakSobolevNorm 4 2 (Lentry θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)) (Nentry θ)≤
                      Centry θ*ENNReal.ofReal ‖f‖ ∧
                    (Lentry θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)
                      =ᵐ[volume.restrict (Nentry θ∩ball (0:E) 1)]u) := by
  dsimp only
  obtain ⟨cTail,m,n,b,S,d₀,CR,CM,C,N,CI,Ccore,Cbase,CY,CSource,χin,χout,χSm,hχin,hχout,hχSm,hcSm,s,O,T₀,L₀,
    hN,hCI,hCore,hCbase,hCY,hCSource,hReceiver,hr,hχone,hχs,h64,hcTail,hmL,hS,hd₀,hC,hModel,hStage⟩:=
    exists_nativeOriginal_scoped_linear_closure g hY gE e he hei hR₀ hsource hcoeff hB hρ hκ0 hκ1 p hp ht
  obtain ⟨dTail,Htail,hdTail,hHtail,hTail⟩:=exists_nativeFinal_inner_tail_H4_bound gE hB hρ hκ0 hκ1 p hp τ T₀ CSource hCSource
  let δ:=min d₀ (dTail/2)
  have hδ:0<δ:=lt_min hd₀ (by linarith)
  refine ⟨cTail,m,n,b,S,δ,CR,CM,C,N,CI,Ccore,Cbase,CY,CSource,χin,χout,χSm,hχin,hχout,hχSm,hcSm,s,O,T₀,L₀,Htail,
    hHtail,hN,hCI,hCore,hCbase,hCY,hCSource,hReceiver,hr,hχone,hχs,h64,hcTail,hmL,hS,hδ,hC,hModel,fun a ha had=>?_⟩
  obtain ⟨ha1,W,hI,hcore,Rbase,Q₀,hfar,hQ₀,hbound,hSm,q,hq,T,hT,hTsmall,hTw,JSm,hJ,hJfix,hJnorm,hSource,hClosure⟩:=
    hStage a ha (had.trans (min_le_left _ _))
  have haTail:a<dTail:=by have h:=had.trans (min_le_right _ _);linarith
  refine ⟨ha1,W,hI,hcore,Rbase,Q₀,hfar,hQ₀,hbound,hSm,q,hq,T,hT,hTsmall,hTw,JSm,hJ,hJfix,hJnorm,hSource,hClosure,?_⟩
  have hχ64:∀x∈closedBall (0:E) 64,χSm x=1:=fun x hx=>hχone x ((closedBall_subset_closedBall h64) hx)
  obtain ⟨Nentry,Lentry,Centry,hFamily,hEntry⟩:=exists_nativeSmoothOriginal_same_entrance_solution
    hκ0 hκ1 p hp W hcoeff hB hρ T₀ O L₀ Q₀ Rbase hModel hQ₀ χSm hχ64 hSm T JSm hJfix hClosure.1 hCSource hSource
  refine ⟨Nentry,Lentry,Centry,hFamily,fun f=>?_⟩
  obtain ⟨u,hum,hrep,hReg,heq,hjet,hEntrance⟩:=hEntry f
  have hY:‖(nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm f).val‖≤CSource*‖f‖:=
    (nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm).le_of_opNorm_le hSource f
  have hTailActual:=hTail a ha.le haTail f _ u hY hReg heq hjet
  exact ⟨u,hum,hrep,hReg,heq,hTailActual,hEntrance⟩

#print axioms exists_nativeOriginal_scoped_linear_full_closure
end Yamabe3.Analysis.SpherePolar
