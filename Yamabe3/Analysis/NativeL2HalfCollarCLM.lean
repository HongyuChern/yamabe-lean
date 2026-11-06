import Yamabe3.Analysis.NativeL2HalfCollarLinear

/-! The actual bounded linear H2 collar jet solver, with the original
same-source field and genuine zero entrance. These are concrete continuous
linear maps into L2, not fields of an assumed solver structure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2HalfCollarValueCLM :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfCollarValueLinear P hplus).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfCollar_uniform_bounds P hplus
    exact ⟨C,fun F => (h F).1⟩)

def nativeL2HalfCollarFirstCLM (j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfCollarFirstLinear P hplus j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfCollar_uniform_bounds P hplus
    exact ⟨G j,fun F => (h F).2.1 j⟩)

def nativeL2HalfCollarSecondCLM (k j : Fin 3) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativeL2HalfCollarSecondLinear P hplus k j).mkContinuousOfExistsBound (by
    obtain ⟨C,G,K,_,_,_,h⟩ := exists_nativeL2HalfCollar_uniform_bounds P hplus
    exact ⟨K k j,fun F => (h F).2.2 k j⟩)

theorem nativeL2HalfCollarCLM_same_field_and_jets
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfCollarCurve P hplus F 0=0 ∧
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (nativeL2HalfCollarCurve P hplus F t : S → ℝ)) ∧
      (nativeL2HalfCollarValueCLM P hplus F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w ∧
      MemWkp 2 2 (nativeL2HalfCollarValueCLM P hplus F) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativeL2HalfCollarFirstCLM P hplus j F)
        (nativeL2HalfCollarValueCLM P hplus F) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativeL2HalfCollarSecondCLM P hplus k j F)
        (nativeL2HalfCollarFirstCLM P hplus j F) nativePoissonEntranceCollar) :=
  exists_nativeL2Half_same_field_H2_zero_entrance P hplus F

#print axioms nativeL2HalfCollarValueCLM
#print axioms nativeL2HalfCollarFirstCLM
#print axioms nativeL2HalfCollarSecondCLM
#print axioms nativeL2HalfCollarCLM_same_field_and_jets
end Yamabe3.Analysis.SpherePolar
