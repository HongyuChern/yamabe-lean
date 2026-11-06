import Yamabe3.Analysis.PhysicalBubbleTailSupport
import Yamabe3.Analysis.NativeSupportedOuterLargeTailCorrection
import Yamabe3.Analysis.NativeCriticalReceiverH4
import Yamabe3.Analysis.NativeCriticalSourceFreeRepresentative
import Yamabe3.Analysis.PhysicalReceiverCost

/-! Same complete outer field -> actual global tail-absorbed correction
-> its same smooth inner representative -> small H4 return. The receiving
radius uses the INNER tail cutoff, not the outgoing cutoff radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def largeTailReceiverH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] largeTailReceiverH1Normed

theorem exists_nativeOuter_large_tail_absorbed_same_receiver_H4
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hsource : closedBall (0 : E) R₀ ⊆ e.source)
    (hcoeff : ∀x∈closedBall (0 : E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (b : ℝ) {τ : ℝ} (ht : 0 < τ) :
    let c := nativeLargeBubbleTailCutoff g hY e he hei (isCompact_closedBall (0 : E) R₀) hsource τ
    ∃T : ℝ, T ≤ -c ∧ ∃δ : ℝ, 0 < δ ∧ ∃C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
        (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt : ℝ ∂volume, t < b → F t=0) →
      ∃w : ℝ×S → ℝ, Measurable w ∧
        (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t : S → ℝ)) ∧
        (∀s : ℝ, NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        ∀(s a : ℝ), s ≤ T → 0 < a → 2*(a*Real.exp (-s)) ≤ R₀ → a*Real.exp c/8 < δ →
        ∀(B : M → ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
          (hsmall : 60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g),
        let Ω := e '' ball (0 : E) (a*Real.exp c/2)
        (∀y∈Ω,B y=0) →
        let Ephys := physicalCutoffSource halfEndBasicAnnulus χ
          (weightedPhysicalDilation s (cylinderLift w)) s a
        let qtail := nativeCompactChartFunction e (closedBall (0 : E) R₀) (fullBubbleScaledTail τ c (Real.log a))
        ∃(W : H1Zero g.leviCivitaData univ) (U : M → ℝ),
          ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U Ω ∧
          U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W : M → ℝ) ∧
          (∀y∈Ω,-8*g.leviCivitaData.laplacian U y+g.leviCivitaData.scalarCurvature y*U y=0) ∧
          (∀η : H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hBs W η =
              ∫x,(nativeCompactChartFunction e (closedBall (0 : E) R₀) Ephys x+
                8*(qtail x*toL2 g.leviCivitaData univ W x))*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure) ∧
          derivativeProfile 2 (ball (0 : E) 1) 4 (fun z => U (e ((a*Real.exp c/8) • z))) ≤
            C*ENNReal.ofReal (Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  let c := nativeLargeBubbleTailCutoff g hY e he hei (isCompact_closedBall (0 : E) R₀) hsource τ
  obtain ⟨T₀,hT₀,C₀,hC₀,h⟩ := exists_nativeSupportedOuter_large_tail_absorbed_correction g hY e he hei
    (isCompact_closedBall (0 : E) R₀) hsource χ hχ b ht
  obtain ⟨δ,hδ,D,hD,hrcv⟩ := exists_nativeCritical_receiver_H4_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  refine ⟨min T₀ (-c),min_le_right _ _,δ,hδ,D*C₀*ENNReal.ofReal (Real.sqrt 8*Real.exp (-c/2)),by finiteness,
    fun F d n σ hσ hF => ?_⟩
  obtain ⟨w,hw,ha,hj,hcorr⟩ := h F d n σ hσ hF
  refine ⟨w,hw,ha,hj,fun s a hs ha' hfit hscale B hBs hsmall => ?_⟩
  dsimp only
  intro hzero
  have hsT : s ≤ T₀ := hs.trans (min_le_left _ _)
  have hsc : s ≤ -c := hs.trans (min_le_right _ _)
  have hRout : Real.exp c ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith only [hsc])
  have hapos : 0 < a*Real.exp c := mul_pos ha' (Real.exp_pos _)
  have hpos : 0 < a*Real.exp (-s) := mul_pos ha' (Real.exp_pos _)
  have hRin : a*Real.exp c ≤ a*Real.exp (-s) := mul_le_mul_of_nonneg_left hRout ha'.le
  have hRR : a*Real.exp c/2 ≤ R₀ := by linarith only [hfit,hpos,hRin]
  have hRRout : a*Real.exp (-s)/2 ≤ R₀ := by linarith only [hfit,hpos]
  have hsrc : ball (0 : E) (a*Real.exp c/2) ⊆ e.source :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRR)).trans hsource
  have hsrcout : ball (0 : E) (a*Real.exp (-s)/2) ⊆ e.source :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hRRout)).trans hsource
  let Ω := e '' ball (0 : E) (a*Real.exp c/2)
  have hΩ : IsOpen Ω := e.isOpen_image_of_subset_source isOpen_ball hsrc
  let Ephys := physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a
  let qtail := nativeCompactChartFunction e (closedBall (0 : E) R₀) (fullBubbleScaledTail τ c (Real.log a))
  obtain ⟨W,hE,hW,hweak⟩ := hcorr s a hsT ha' B hBs hsmall
  have hEzero : ∀y∈Ω,nativeCompactChartFunction e (closedBall (0 : E) R₀) Ephys y=0 := by
    intro y hy
    apply native_physicalCutoffSource_zero_inner e χ (weightedPhysicalDilation s (cylinderLift w)) s a ha' _ hsrcout y
    exact image_mono (ball_subset_ball (by linarith only [hRin])) hy
  have hqzero : ∀y∈Ω,qtail y=0 :=
    native_physicalBubbleTail_zero_inner e (closedBall (0 : E) R₀) τ c a ha' (by linarith only [hapos]) hsrc
  have hfullzero : ∀y∈Ω,nativeCompactChartFunction e (closedBall (0 : E) R₀) Ephys y+
      8*(qtail y*toL2 g.leviCivitaData univ W y)=0 := by
    intro y hy
    rw [hEzero y hy,hqzero y hy,zero_mul,mul_zero,add_zero]
  obtain ⟨U,hU,hUAE,hP⟩ := exists_nativeCritical_sourceFree_representative g B hBs W _ hweak hΩ hfullzero
  have hPe : ∀y∈Ω,-8*g.leviCivitaData.laplacian U y+g.leviCivitaData.scalarCurvature y*U y=0 := by
    intro y hy
    have hh := hP y hy
    simpa only [hzero y hy,zero_pow (by decide : 4≠0),mul_zero,sub_zero] using hh
  have hH4 := hrcv (a*Real.exp c/2) (by positivity) hRR W Ω hΩ U hU hUAE
    (fun x hx => mem_image_of_mem e hx) (fun x hx => hPe _ (mem_image_of_mem e hx))
    (a*Real.exp c/8) (by positivity) hscale (by linarith only [hapos])
  refine ⟨W,U,hU,hUAE,hPe,hweak,?_⟩
  apply hH4.trans
  apply (mul_le_mul le_rfl hW zero_le zero_le).trans_eq
  have he : ENNReal.ofReal (Real.exp (-Real.log (a*Real.exp c/8)/2))*ENNReal.ofReal (Real.sqrt a) =
      ENNReal.ofReal (Real.sqrt 8*Real.exp (-c/2)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simpa only [neg_neg,neg_div] using physicalReceiver_sqrt_cost a ha' (-c)
  rw [mul_assoc (Real.sqrt a),ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc
    _ = D*C₀*(ENNReal.ofReal (Real.exp (-Real.log (a*Real.exp c/8)/2))*ENNReal.ofReal (Real.sqrt a))*
      ENNReal.ofReal (Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖)) := by ring
    _ = _ := by rw [he]

#print axioms exists_nativeOuter_large_tail_absorbed_same_receiver_H4
end Yamabe3.Analysis.SpherePolar
