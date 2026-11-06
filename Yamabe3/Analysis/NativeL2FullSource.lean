import Yamabe3.Analysis.NativeL2PhysicalSource

/-! The true full and low angular source lifts on the same L2 source
space. Their sum is the full lift, without a source regularity assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeL2LowAngularCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularL2 2 (volume : Measure ℝ) :=
  (nativeLowProjection.comp angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap).compLpL 2 volume

def nativeL2FullAngularCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularL2 2 (volume : Measure ℝ) :=
  angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.compLpL 2 volume

def nativeL2LowPhysicalSourceCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2CollarLiftCLM.comp nativeL2LowAngularCLM

def nativeL2FullPhysicalSourceCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2CollarLiftCLM.comp nativeL2FullAngularCLM

theorem nativeL2LowAngularCLM_ae (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (nativeL2LowAngularCLM F : ℝ → AngularL2)=ᵐ[volume]
      (fun t => nativeLowProjection (angularBasis.repr.symm (F t))) :=
  (nativeLowProjection.comp angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap).coeFn_compLpL F

theorem nativeL2FullAngularCLM_ae (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (nativeL2FullAngularCLM F : ℝ → AngularL2)=ᵐ[volume](fun t => angularBasis.repr.symm (F t)) :=
  angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL F

theorem nativeL2LowPhysicalSource_eq_lift (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (nativeLowProjection (angularBasis.repr.symm (F t)) : S → ℝ)) :
    (nativeL2LowPhysicalSourceCLM F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  apply nativeL2CollarLift_eq_lift _ hw
  filter_upwards [hae,nativeL2LowAngularCLM_ae F] with t ht hF
  change (fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2LowAngularCLM F t : S → ℝ)
  rw [hF]
  exact ht

theorem nativeL2FullPhysicalSource_eq_lift (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume]
      (angularBasis.repr.symm (F t) : S → ℝ)) :
    (nativeL2FullPhysicalSourceCLM F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  apply nativeL2CollarLift_eq_lift _ hw
  filter_upwards [hae,nativeL2FullAngularCLM_ae F] with t ht hF
  change (fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2FullAngularCLM F t : S → ℝ)
  rw [hF]
  exact ht

theorem nativeL2High_add_low_source (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeL2HighPhysicalSourceCLM F+nativeL2LowPhysicalSourceCLM F=nativeL2FullPhysicalSourceCLM F := by
  have he : nativeL2HighAngularCLM F+nativeL2LowAngularCLM F=nativeL2FullAngularCLM F := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (nativeL2HighAngularCLM F) (nativeL2LowAngularCLM F),
      nativeL2HighAngularCLM_ae F,nativeL2LowAngularCLM_ae F,nativeL2FullAngularCLM_ae F] with t ha hh hl hf
    rw [ha]
    change nativeL2HighAngularCLM F t+nativeL2LowAngularCLM F t=nativeL2FullAngularCLM F t
    rw [hh,hl,hf,nativeHighProjection_add_low]
  change nativeL2CollarLiftCLM (nativeL2HighAngularCLM F)+nativeL2CollarLiftCLM (nativeL2LowAngularCLM F)=nativeL2CollarLiftCLM (nativeL2FullAngularCLM F)
  exact (nativeL2CollarLiftCLM.map_add (nativeL2HighAngularCLM F) (nativeL2LowAngularCLM F)).symm.trans
    (congrArg (fun H => nativeL2CollarLiftCLM H) he)

#print axioms nativeL2LowAngularCLM_ae
#print axioms nativeL2FullAngularCLM_ae
#print axioms nativeL2LowPhysicalSource_eq_lift
#print axioms nativeL2FullPhysicalSource_eq_lift
#print axioms nativeL2High_add_low_source
end Yamabe3.Analysis.SpherePolar
