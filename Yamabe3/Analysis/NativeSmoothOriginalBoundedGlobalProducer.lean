import Yamabe3.Analysis.NativeOrderedEnergyTraceProducer
import Yamabe3.Analysis.NativeFinalFeedbackSourceMap
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
import Yamabe3.Analysis.NativeSmoothPotentialUniformGap
import Yamabe3.Analysis.NativeSmoothPotentialFeedback
import Yamabe3.Analysis.NativeOrderedEnergyProducer
import Yamabe3.Analysis.NativeOrderedEnergySourceFeedback
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization

/-! One ACTUALLY PRODUCED signed native completed field for the original
weighted H2 source. All baseline/correction/return maps share one source,
one tail and one receiving space. The uniform energy bound is proved;
the full native PDE and global quotient-conormal identity remain gates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def signedOriginalNormed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] signedOriginalNormed


private instance producer32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
theorem exists_nativeSmoothOriginal_bounded_global_producer
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
      (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O),
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
            NativeSmoothOriginalGlobalRealization hκ0 hκ1 p hp W T₀ Q₀ Rbase χSm hSm T JSm := by
  dsimp only
  obtain ⟨cTail,m,n,b,S,d₀,CR,CM,C,N,CI,Ccore,Cbase,CY,χin,χout,hχin,hχout,O,T₀,L₀,hN,hCI,hCore,hCbase,hCY,hReceiver,hcTail,hmL,hSComp,hd₀,hC,hModel,hStage⟩:=
    exists_nativeOriginal_signed_energy_trace_producer g hY gE e he hei hR₀ hsource hcoeff hB hρ hκ0 hκ1 p hp ht
  obtain ⟨ha₀1,W₀,hI₀,hCore₀,Rb₀,Q₀₀,hRb₀,hYC₀,hfar₀,hQ₀₀,hbound₀,hfix₀⟩:=hStage (d₀/2) (by linarith) (by linarith)
  have hCM:0≤CM:=by
    have hn:0≤CM*Real.sqrt (d₀/2):=W₀.Q.opNorm_nonneg.trans W₀.native_field_bound
    nlinarith [Real.sqrt_pos.2 (show 0<d₀/2 by linarith)]
  have hCR:0≤CR:=by
    have hn:0≤CR*Real.sqrt (d₀/2):=W₀.R.opNorm_nonneg.trans W₀.return_bound
    nlinarith [Real.sqrt_pos.2 (show 0<d₀/2 by linarith)]
  let Cost:=4*CM*CI+(Ccore+1)*(1+4*CR*CI)
  have hCost:1≤Cost:=by
    have h0:0≤4*CM*CI:=by positivity
    have h1:0≤4*CR*CI:=by positivity
    have h2:0≤Ccore*(4*CR*CI):=mul_nonneg hCore h1
    dsimp only [Cost]
    nlinarith
  let CSource:=CY*‖T₀‖+4*CI*C
  have hCSource:0≤CSource:=by dsimp only [CSource];positivity
  let Budget:=Cost*N
  have hBudget:0≤Budget:=by dsimp only [Budget,Cost];positivity
  obtain ⟨s,χSm,hχSm,hcSm,dSm,hs,h64,hdSm,hr,hχone,hχs,hSmStage⟩:=exists_nativeSmoothPotential_uniform_strict_gap
    g hY e he hei hR₀ hsource τ (-S+1/4) Budget hBudget
  let H:=Real.exp (((m+n:ℕ):ℝ)/2+1)
  let Htail:=Real.exp cTail+1
  let δ:=min d₀ (min dSm (min (R₀/H) (R₀/Htail)))
  have hH:0<H:=Real.exp_pos _
  have hHt:0<Htail:=by dsimp only [Htail];positivity
  have hδ:0<δ:=by dsimp only [δ];positivity
  refine ⟨cTail,m,n,b,S,δ,CR,CM,C,N,CI,Ccore,Cbase,CY,CSource,χin,χout,χSm,hχin,hχout,hχSm,hcSm,s,O,T₀,L₀,
    hN,hCI,hCore,hCbase,hCY,hCSource,hReceiver,hr,hχone,hχs,h64,hcTail,hmL,hSComp,hδ,hC,hModel,fun a ha had=>?_⟩
  obtain ⟨ha1,W,hI,hcore,Rbase,Q₀,hRb,hYC,hfar,hQ₀,hbound,hfix⟩:=hStage a ha (had.trans (min_le_left _ _))
  have haSm:a≤dSm:=had.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haH:a≤R₀/H:=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haHt:a≤R₀/Htail:=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀:=(le_div_iff₀ hH).mp haH
  have hfitTail:a*(Real.exp cTail+1)≤R₀:=(le_div_iff₀ hHt).mp haHt
  obtain ⟨hSupp,hSm,q,hq,hgap⟩:=hSmStage a ha haSm
  have hBallK:closedBall (0:E) (a*Real.exp s)⊆closedBall (0:E) R₀:=by
    intro x hx
    have hxU:a⁻¹ • x∈closedBall (0:E) (Real.exp s):=by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
      exact (inv_mul_le_iff₀ ha).mpr (mem_closedBall_zero_iff.mp hx)
    apply hSupp
    apply subset_tsupport
    change χSm (a⁻¹ • x)≠0
    rw [hχone _ hxU]
    norm_num
  obtain ⟨T,hT,hTw,JSm,hJ,hJfix⟩:=exists_nativeSmoothPotential_energy_feedback W hY hN.le hCI hCM hCR hCore hI hcore hReceiver
    h64 χSm hχone hSupp hBallK q hq hgap
  have hTsmall:‖T‖≤1/2:=by
    apply hT.trans
    calc
      _≤Cost*(N*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖)):=
        le_mul_of_one_le_left (by positivity) hCost
      _=Budget*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖):=by dsimp only [Budget];ring
      _≤1/2:=hgap
  refine ⟨ha1,W,hI,hcore,Rbase,Q₀,hfar,hQ₀,hbound,hSm,q,hq,T,hT,hTsmall,hTw,JSm,hJ,hJfix,?_,?_,?_⟩
  · calc
      _≤‖JSm‖*‖nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase‖:=ContinuousLinearMap.opNorm_comp_le _ _
      _≤2*(C*Real.sqrt a):=mul_le_mul hJ hbound (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase).opNorm_nonneg (by norm_num)
      _=(2*C)*Real.sqrt a:=by ring
  · exact nativeFinalFeedbackSourceCLM_uniform_bound W T₀ Q₀ Rbase T JSm hCY hCI hC hYC hI hTsmall hJ hbound
  · intro f
    obtain ⟨F,hF,hTF,hFa,qi,wo,hqi,hwo,hbi,hbo,hLE⟩:=hModel f
    exact exists_nativeSmoothOriginal_same_global_solution hκ0 hκ1 p hp W hY χSm hSm q hq T hTw JSm hJfix
      hcoeff hfit hfitTail hcTail Rbase hfar T₀ Q₀ O L₀ hQ₀ hB hρ hModel f F qi wo hLE hbo

#print axioms exists_nativeSmoothOriginal_bounded_global_producer
end Yamabe3.Analysis.SpherePolar
