import Yamabe3.Analysis.NativeL2ParticularNormBounds
import Yamabe3.Analysis.NativeL2ParticularModeLinearity
import Yamabe3.Analysis.NativeC2CollarValueLinear
import Yamabe3.Analysis.L2ContinuousSourceModule
import Yamabe3.Analysis.L2WeakDerivativeLinear

/-! The already constructed same-field H2 jets are linear in the actual
continuous L2 source. Derivative linearity follows from uniqueness in
the same restricted-volume L2 space, not from independent jet choices. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

theorem nativeL2ParticularCollarValue_add
    (F G : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) (hG : MemLp G 2) :
    nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus (F+G) (hF.add hG)=
      nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF+
        nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus G hG := by
  unfold nativeL2ParticularCollarValue
  rw [←Summable.tsum_add (nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus F hF).1
    (nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus G hG).1]
  apply tsum_congr
  intro i
  apply nativeC2CollarValue_add
  exact nativeL2ParticularMode_add hκ0 hκ1 V hminus F G i

theorem nativeL2ParticularCollarValue_smul
    (c : ℝ) (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) :
    nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus (c • F) (hF.const_smul c)=
      c • nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF := by
  unfold nativeL2ParticularCollarValue
  rw [←Summable.tsum_const_smul c (nativeL2ParticularCollar_modes_summable hκ0 hκ1 V hminus hplus F hF).1]
  apply tsum_congr
  intro i
  apply nativeC2CollarValue_smul
  exact nativeL2ParticularMode_smul hκ0 hκ1 V hminus c F i

def nativeL2ParticularValueLinear :
    continuousL2Source (SpectralSpace AngularIndex) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) where
  toFun F := nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F.val F.property
  map_add' F G := nativeL2ParticularCollarValue_add hκ0 hκ1 V hminus hplus F.val G.val F.property G.property
  map_smul' c F := nativeL2ParticularCollarValue_smul hκ0 hκ1 V hminus hplus c F.val F.property

def nativeL2ParticularFirstLinear (j : Fin 3) :
    continuousL2Source (SpectralSpace AngularIndex) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j
    (nativeL2ParticularValueLinear hκ0 hκ1 V hminus hplus)
    (fun F => nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F.val F.property j)
    (fun F => (nativeL2ParticularCollar_H2_and_jets hκ0 hκ1 V hminus hplus F.val F.property).2.1 j)

def nativeL2ParticularSecondLinear (k j : Fin 3) :
    continuousL2Source (SpectralSpace AngularIndex) →ₗ[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k
    (nativeL2ParticularFirstLinear hκ0 hκ1 V hminus hplus j)
    (fun F => nativeL2ParticularCollarSecond hκ0 hκ1 V hminus hplus F.val F.property k j)
    (fun F => (nativeL2ParticularCollar_H2_and_jets hκ0 hκ1 V hminus hplus F.val F.property).2.2 k j)

#print axioms nativeL2ParticularCollarValue_add
#print axioms nativeL2ParticularCollarValue_smul
#print axioms nativeL2ParticularValueLinear
#print axioms nativeL2ParticularFirstLinear
#print axioms nativeL2ParticularSecondLinear
end Yamabe3.Analysis.SpherePolar
