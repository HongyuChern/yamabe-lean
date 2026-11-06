import Yamabe3.Analysis.NativeFullMatchedAllScale
import Yamabe3.Analysis.NativeDelaunayJacobianRowBinding

/-! The coupled boundary correction and full particular solution share one actual orbit, source, and scale family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)

def nativeMatchedDelaunayRawJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeFullMatchedAllScaleRawJetCLM B (p.nativeHighPotential hκ0 hκ1) hp (fun t => p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) s

def nativeMatchedDelaunayJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeFullMatchedAllScaleJetCLM B (p.nativeHighPotential hκ0 hκ1) hp (fun t => p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) s

theorem nativeMatchedDelaunay_memH2 (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeMatchedDelaunayJetCLM hκ0 hκ1 B p hp s F)

theorem nativeMatchedDelaunay_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧ ∀ s : ℝ,
      ((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) :=
  exists_nativeFullMatchedAllScale_same_field B (p.nativeHighPotential hκ0 hκ1) hp _ _ _ F

theorem nativeMatchedDelaunay_physical_equation (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s
      ((∑ j : Fin 3,(nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).2.2 j j)+
        nativeCollarPotentialMulCLM (delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+s))
          (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1)=
      nativePositiveScaledRestrictionCLM s (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) := by
  have he : (p.nativeHighPotential hκ0 hκ1).potential=
      delaunayPhasePotentialBCF (fun t => p.orbit (t+p.phase))
        (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) 0 := by
    apply BoundedContinuousFunction.ext
    intro t
    change (15/4)*p.orbit (t+p.phase)^4=(15/4)*p.orbit (t+0+p.phase)^4
    rw [add_zero]
  have h := nativeFullMatchedAllScale_equation B (p.nativeHighPotential hκ0 hκ1) hp _ _ _ he s F
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,(nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).2.2 j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s p.potential)
        (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1)=_ at h
  rwa [delaunayPhasePotential_time_translate] at h

omit B p hp in
theorem exists_uniform_nativeMatchedDelaunayJet_bound :
    ∃ L : ℝ,0<L ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (s : ℝ),
        ‖nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s‖≤L := by
  obtain ⟨L,hL,h⟩ := exists_family_nativeFullMatchedAllScale_bound hκ0 hκ1 (M := 15/4) (by norm_num)
  exact ⟨L,hL,fun B p hp s => h B (p.nativeHighPotential hκ0 hκ1) rfl
    (delaunayPhasePotentialBCF_norm_le p.orbit p.smooth.continuous p.bounded p.phase) hp _ _ _ s⟩

#print axioms nativeMatchedDelaunay_memH2
#print axioms nativeMatchedDelaunay_same_field
#print axioms nativeMatchedDelaunay_physical_equation
#print axioms exists_uniform_nativeMatchedDelaunayJet_bound
end Yamabe3.Analysis.SpherePolar
