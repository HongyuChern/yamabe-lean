import Yamabe3.Analysis.NativeSupportedOuterNewtonCutoff
import Yamabe3.Analysis.NativeLargeBubbleTailSolution
import Yamabe3.Analysis.NativeChartCriticalTransport

/-! The actual Newton-decaying complete outer field supplies a physical
factor-eight cutoff source to the constructed global tail-absorbed
native inverse. Same source, same native completed element, all tests.
Geometry errors and the full boundary feedback are not omitted into a PASS. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff Manifold ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def largeTailCorrectionH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] largeTailCorrectionH1Normed
private instance largeTailCorrection65 : Fact (1 ≤ (6/5 : ℝ≥0∞)) := ⟨one_le_sixFifths⟩

theorem exists_nativeSupportedOuter_large_tail_absorbed_correction
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (b : ℝ) {τ : ℝ} (ht : 0 < τ) :
    ∃T : ℝ, T ≤ -(1/2 : ℝ) ∧ ∃C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
        (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt : ℝ ∂volume, t < b → F t=0) →
      ∃w : ℝ×S → ℝ, Measurable w ∧
        (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t : S → ℝ)) ∧
        (∀s : ℝ, NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        ∀(s a : ℝ), s ≤ T → 0 < a →
        ∀(B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
          (hsmall : 60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g),
        let Ephys := physicalCutoffSource halfEndBasicAnnulus χ
          (weightedPhysicalDilation s (cylinderLift w)) s a
        let qtail := nativeCompactChartFunction e K
          (fullBubbleScaledTail τ (nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ) (Real.log a))
        ∃W : H1Zero g.leviCivitaData univ,
          MemLp Ephys (6/5 : ℝ≥0∞) volume ∧
          ENNReal.ofReal ‖W‖ ≤ C*ENNReal.ofReal (Real.sqrt a*Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖)) ∧
          ∀η : H1Zero g.leviCivitaData univ,
            closedYamabeJacobianForm g B hB W η =
              ∫x,(nativeCompactChartFunction e K Ephys x+8*(qtail x*toL2 g.leviCivitaData univ W x))*
                toL2 g.leviCivitaData univ η x ∂g.volumeMeasure := by
  obtain ⟨T,hT,C₀,hC₀,h⟩ := exists_nativeSupportedOuter_Newton_cutoff_bound χ hχ b ht
  obtain ⟨D,hD,hd⟩ := exists_nativeCompactChart_critical_bound g e he hei hK hKs
  obtain ⟨N,hN,hn⟩ := exists_uniform_closedSixFifthsJacobianSolution_bound g hY
  refine ⟨T,hT,ENNReal.ofReal (2*N)*D*C₀,by finiteness,fun F d n σ hσ hF => ?_⟩
  obtain ⟨w,hw,ha,hj,hsrc⟩ := h F d n σ hσ hF
  refine ⟨w,hw,ha,hj,fun s a hs ha' B hB hsmall => ?_⟩
  let Ephys := physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a
  have hE := hsrc s a hs ha'
  have hG := hd Ephys hE.1
  let G := hG.1.toLp (nativeCompactChartFunction e K Ephys)
  let L := nativeLargeBubbleTailSolutionCLM g hY e he hei hK hKs τ B hB hsmall (Real.log a)
  let W := L G
  have hOp : ‖L‖ ≤ 2*N :=
    (nativeLargeBubbleTailSolutionCLM_norm g hY e he hei hK hKs τ B hB hsmall (Real.log a)).trans
      (mul_le_mul_of_nonneg_left (hn B hB hsmall).1 (by norm_num))
  have hW : ENNReal.ofReal ‖W‖ ≤ ENNReal.ofReal (2*N)*ENNReal.ofReal ‖G‖ := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*N)]
    exact ENNReal.ofReal_le_ofReal ((L.le_opNorm G).trans (mul_le_mul_of_nonneg_right hOp (norm_nonneg G)))
  have hGn : ENNReal.ofReal ‖G‖ = eLpNorm (nativeCompactChartFunction e K Ephys) (6/5 : ℝ≥0∞) g.volumeMeasure := by
    rw [ofReal_norm]
    exact Lp.enorm_toLp hG.1
  refine ⟨W,hE.1,?_,?_⟩
  · rw [hGn] at hW
    exact hW.trans ((mul_le_mul le_rfl (hG.2.trans (mul_le_mul le_rfl hE.2 zero_le zero_le)) zero_le zero_le).trans_eq (by ring))
  · intro η
    have hh := nativeLargeBubbleTailSolutionCLM_weak g hY e he hei hK hKs τ B hB hsmall (Real.log a) G η
    refine hh.trans (integral_congr_ae ?_)
    filter_upwards [hG.1.coeFn_toLp] with x hx
    change (G x+_)*_ = _
    rw [show G x=nativeCompactChartFunction e K Ephys x from hx]

#print axioms exists_nativeSupportedOuter_large_tail_absorbed_correction
end Yamabe3.Analysis.SpherePolar
