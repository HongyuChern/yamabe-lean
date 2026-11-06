import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4ValueSourceIdentity
import Yamabe3.Analysis.NativeH4LocalSourceEquation

/-! The actual INNER residual cancellation needs only the inner source
fixed point. The independent finite outer/far/incoming construction is
retained; no obsolete full-collar exterior fixed point is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedJacobianRowCLM
  nativeH4MatchedGeometricSourceTerm
section OriginalPhase
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v₀" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))
local notation "O" => (Metric.ball (0:E) 1 \ {(0:E)})

include b ht in
theorem nativeH4ValueCorrected_local_source_identity
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hfix : Y.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v₀ hv hb τ (g a) ε Y)
    (F u : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue x)) F (Metric.closedBall (0:E) 4))
    (hu : ∀i : HalfEndPhysicalSliceIndex,
      ((nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y i).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun y => Real.exp (3*i.1/2)*u (Real.exp (-i.1) • y))) :
    MemWkpLocally 2 u O ∧ ∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆O →
      MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U (g a) ε p.orbit p.phase u
        =ᵐ[volume.restrict U] nativeWeakFlatJacobian U p.orbit p.phase F := by
  have hpot : (P).potential=delaunayPhasePotentialBCF v₀ hv hb 0 := by
    apply BoundedContinuousFunction.ext
    intro t
    change (15/4)*p.orbit (t+p.phase)^4=(15/4)*p.orbit (t+0+p.phase)^4
    rw [add_zero]
  have hid := nativeH4ValueResidual_same_physical_operators hκ0 hκ1 p hp τ (g a) ε x Y F u hF hu
  have hz := (nativeH4Residual_physical_zero_partial P hp v₀ hv hb b ht hpot Λ g hB hρ ε hε hε1 a ha x Y hfix).2
  have hop : nativePhysicalWeakJacobian (g a) ε p.orbit p.phase u=ᵐ[volume.restrict O]
      nativePhysicalWeakFlatJacobian p.orbit p.phase F := by
    filter_upwards [hid,hz] with y hi hz
    exact sub_eq_zero.mp (hi.symm.trans hz)
  have hul := native_half_scale_jet_local_H2 (fun i => nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y i) hu
  have hFl := native_half_scale_jet_local_H2 (fun i => nativeH4GraphScaleJetCLM i x)
    (fun i => nativeH4GraphScaleJet_same_function i x F hF)
  have huw (n : ℕ) := native_true_scale_jet_physical_H2 (nativeLogShellCenter n)
    (nativeH4ValueCorrectedJet P hp v₀ hv hb τ x Y
      (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)))
    (hu (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)))
  have hFw (n : ℕ) := native_true_scale_jet_physical_H2 (nativeLogShellCenter n)
    (nativeH4GraphScaleJetCLM (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)) x)
    (nativeH4GraphScaleJet_same_function _ x F hF)
  refine ⟨hul,fun U hU hUc hUO => ?_⟩
  have huU := memWkp_on_precompact_of_locally hul hU hUc hUO
  have hFU := memWkp_on_precompact_of_locally hFl hU hUc hUO
  have hUN := nativePhysicalWeakJacobian_local hU huU huw (g a) ε p.orbit p.phase
  have hUF := nativePhysicalWeakFlatJacobian_local hU hFU hFw p.orbit p.phase
  have hs : U∩O=U := inter_eq_left.mpr (subset_closure.trans hUO)
  rw [hs] at hUN hUF
  have hopU : nativePhysicalWeakJacobian (g a) ε p.orbit p.phase u=ᵐ[volume.restrict U]
      nativePhysicalWeakFlatJacobian p.orbit p.phase F :=
    ae_mono (Measure.restrict_mono (subset_closure.trans hUO) le_rfl) hop
  exact ⟨huU,hUN.symm.trans (hopU.trans hUF)⟩


#print axioms nativeH4ValueCorrected_local_source_identity
end OriginalPhase
end Yamabe3.Analysis.UniformElliptic
