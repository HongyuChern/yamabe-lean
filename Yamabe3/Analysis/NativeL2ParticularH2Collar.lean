import Yamabe3.Analysis.NativeL2ParticularModeBudget

/-! One actual H2 collar value and its actual weak first/second derivatives
for the high part of the same continuous L2 particular field. Strong
finite-mode convergence, rather than separate existence claims, binds
all derivative limits to the same value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
  (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2)

def nativeL2ParticularCollarValue : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarValue (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i)
def nativeL2ParticularCollarFirst (j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarFirst (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i) j
def nativeL2ParticularCollarSecond (k j : Fin 3) : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ∑' i,nativeC2CollarSecond (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i) k j

theorem nativeL2ParticularCollar_modes_summable :
    Summable (fun i => nativeC2CollarValue (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i)) ∧
    (∀ j,Summable (fun i => nativeC2CollarFirst (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i) j)) ∧
    (∀ k j,Summable (fun i => nativeC2CollarSecond (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF i) k j)) := by
  apply nativeC2Collar_series_summable _ _
    (nativeL2ParticularModeBudget_summable hκ0 hκ1 V hminus hplus F hF)
    (nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus F) (by norm_num : (0:ℝ)≤1)
  intro s
  simpa only [one_mul] using nativeL2ParticularMode_finite_budget hκ0 hκ1 V hminus hplus F hF s

theorem nativeL2ParticularCollar_H2_and_jets :
    MemWkp 2 2 (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF) nativePoissonEntranceCollar ∧
    (∀ j,HasWeakPartialDeriv j (nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F hF j)
      (nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF) nativePoissonEntranceCollar) ∧
    (∀ k j,HasWeakPartialDeriv k (nativeL2ParticularCollarSecond hκ0 hκ1 V hminus hplus F hF k j)
      (nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F hF j) nativePoissonEntranceCollar) := by
  apply nativeC2Collar_series_H2 _ _
    (nativeL2ParticularModeBudget_summable hκ0 hκ1 V hminus hplus F hF)
    (nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus F) (by norm_num : (0:ℝ)≤1)
  intro s
  simpa only [one_mul] using nativeL2ParticularMode_finite_budget hκ0 hκ1 V hminus hplus F hF s

#print axioms nativeL2ParticularCollar_modes_summable
#print axioms nativeL2ParticularCollar_H2_and_jets
end Yamabe3.Analysis.SpherePolar
