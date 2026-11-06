import Yamabe3.Analysis.NativeAllScaleJetClosure
import Yamabe3.Analysis.NativePoissonAllScaleEquation
import Yamabe3.Analysis.NativeL2PotentialBinding

/-! The same all-L2 half field satisfies the shifted physical equation
on exactly the positive-time part of every collar, with the original
source translation and the coefficient eight unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (s : ℝ)

theorem nativeL2HalfAllScale_physical_equation
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s ((∑ j : Fin 3,nativeL2HalfAllScaleSecondCLM P hplus s j j F)+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativeL2HalfAllScaleValueCLM P hplus s F))=
        nativePositiveScaledRestrictionCLM s (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)) := by
  let b := nativeL2HalfEntrance P hplus F
  have hp := nativeL2Particular_physical_equation P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
  have hz := nativePoissonAllScale_homogeneous P hplus s b
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1
  change nativePositiveScaledRestrictionCLM s
    ((∑ j : Fin 3,(nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) j j
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)-
      nativePoissonAllScaleSecond P hplus s b j j))+
      nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
        (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)-nativePoissonAllScaleValue P hplus s b))=_
  rw [Finset.sum_sub_distrib,map_sub]
  have he : ((∑ j : Fin 3,nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) j j
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))-
      (∑ j : Fin 3,nativePoissonAllScaleSecond P hplus s b j j))+
      (nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
        (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))-
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativePoissonAllScaleValue P hplus s b))=
      ((∑ j : Fin 3,nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s) j j
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)
          (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one (boundedTimeTranslate ℝ s P.potential)
      (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hplus s)
      (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)))-
      ((∑ j : Fin 3,nativePoissonAllScaleSecond P hplus s b j j)+
        nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativePoissonAllScaleValue P hplus s b)) := by abel
  rw [he,map_sub,hp,hz,sub_zero]

theorem nativeL2HalfAllScale_physical_equation_eight
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativePositiveScaledRestrictionCLM s
      ((-8:ℝ) • (∑ j : Fin 3,nativeL2HalfAllScaleSecondCLM P hplus s j j F)-
        (8:ℝ) • nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential) (nativeL2HalfAllScaleValueCLM P hplus s F))=
      (-8:ℝ) • nativePositiveScaledRestrictionCLM s (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)) := by
  have h := congrArg (fun x => (-8:ℝ) • x) (nativeL2HalfAllScale_physical_equation P hplus s F)
  rw [map_add,smul_add] at h
  simpa only [map_sub,map_smul,neg_smul,sub_eq_add_neg,map_add,map_neg] using h

#print axioms nativeL2HalfAllScale_physical_equation
#print axioms nativeL2HalfAllScale_physical_equation_eight
end Yamabe3.Analysis.SpherePolar
