import Yamabe3.Analysis.NativeFullL2Collar
import Yamabe3.Analysis.NativeDelaunayJacobianRowBinding

/-! The high and low solvers use the literal same Delaunay orbit and
phase. The operator equality is discharged, not supplied as an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)

def nativeFullDelaunayRawJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarJet :=
  nativeFullL2AllScaleRawJetCLM (p.nativeHighPotential hκ0 hκ1) hp (fun t => p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) s

def nativeFullDelaunayJetCLM (s : ℝ) : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeFullL2AllScaleJetCLM (p.nativeHighPotential hκ0 hκ1) hp (fun t => p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) s

theorem nativeFullDelaunay_memH2 (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemWkp 2 2 (nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeFullDelaunayJetCLM hκ0 hκ1 p hp s F)

theorem nativeFullDelaunay_same_field (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ∃ w : ℝ × S → ℝ,Measurable w ∧ ∀ s : ℝ,
      ((nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) :=
  exists_nativeFullL2AllScale_same_field (p.nativeHighPotential hκ0 hκ1) hp _ _ _ F

theorem nativeFullDelaunay_physical_equation (s : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s
      ((∑ j : Fin 3,(nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).2.2 j j)+
        nativeCollarPotentialMulCLM (delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+s))
          (nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).1)=
      nativePositiveScaledRestrictionCLM s (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F)) := by
  have he : (p.nativeHighPotential hκ0 hκ1).potential=
      delaunayPhasePotentialBCF (fun t => p.orbit (t+p.phase))
        (p.smooth.continuous.comp (continuous_id.add continuous_const)) (fun t => p.bounded (t+p.phase)) 0 := by
    apply BoundedContinuousFunction.ext
    intro t
    change (15/4)*p.orbit (t+p.phase)^4=(15/4)*p.orbit (t+0+p.phase)^4
    rw [add_zero]
  have h := nativeFullL2AllScale_equation (p.nativeHighPotential hκ0 hκ1) hp _ _ _ he s F
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,(nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).2.2 j j)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s p.potential)
        (nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s F).1)=_ at h
  rwa [delaunayPhasePotential_time_translate] at h

omit p hp in
theorem exists_uniform_nativeFullDelaunayJet_bound :
    ∃ B : ℝ,0<B ∧ ∀ (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (s : ℝ),
        ‖nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp s‖≤B := by
  obtain ⟨B,hB,h⟩ := exists_family_nativeFullL2AllScale_bound hκ0 hκ1 (M := 15/4) (by norm_num)
  exact ⟨B,hB,fun p hp s => h (p.nativeHighPotential hκ0 hκ1) rfl
    (delaunayPhasePotentialBCF_norm_le p.orbit p.smooth.continuous p.bounded p.phase) hp _ _ _ s⟩

#print axioms nativeFullDelaunay_memH2
#print axioms nativeFullDelaunay_same_field
#print axioms nativeFullDelaunay_physical_equation
#print axioms exists_uniform_nativeFullDelaunayJet_bound
end Yamabe3.Analysis.SpherePolar
