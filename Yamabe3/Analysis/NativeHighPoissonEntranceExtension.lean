import Yamabe3.Analysis.NativeHighPoissonJetEnergy
import Yamabe3.Analysis.HalfLineC2Reflection
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Actual Poisson entrance jets and their C² reflection. The right
second derivative at zero follows from the ODE and continuity; it is
not a boundary regularity assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem NativeHighPotential.coordinate_continuous (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) : Continuous (nativePoissonCoordinate P b i) := by
  apply (innerSL ℝ (angularBasis i)).continuous.comp
  change Continuous (fun t : ℝ => Real.exp (-2*t) •
    nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
      P.kernel_bound P.nonneg b t.toNNReal)
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
      P.kernel_bound P.nonneg b).continuous.comp continuous_real_toNNReal)

theorem NativeHighPotential.coordinate_second_right_jet (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => inner ℝ (angularBasis i) (P.curveDerivative b s))
      ((nativeAngularRate i^2-P.potential t)*nativePoissonCoordinate P b i t) (Ici 0) t := by
  let D := fun s => inner ℝ (angularBasis i) (P.curveDerivative b s)
  let a := fun s => (nativeAngularRate i^2-P.potential s)*nativePoissonCoordinate P b i s
  have hD : Continuous D := (innerSL ℝ (angularBasis i)).continuous.comp
    (nativeHalfHighPotentialPhysicalDerivative_continuous P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b)
  have ha : Continuous a := (continuous_const.sub P.potential.continuous).mul
    (P.coordinate_continuous b i)
  have hode : ∀ s : ℝ, 0 < s → HasDerivAt D (a s) s :=
    nativeHalfHighPotentialPhysical_derivative_equation P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b i
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
      (fun s hs => (hode s hs).differentiableAt.differentiableWithinAt)
      hD.continuousAt.continuousWithinAt self_mem_nhdsWithin
    apply (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hode s hs).deriv.symm
  · exact (hode t ht).hasDerivWithinAt

def nativePoissonEntranceExtension (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) : ℝ → ℝ := halfLineC2Extension (nativePoissonCoordinate P b i)

theorem NativeHighPotential.entranceExtension_C2 (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) : ContDiff ℝ 2 (nativePoissonEntranceExtension P b i) := by
  apply halfLineC2Extension_contDiff
    (df := fun t => inner ℝ (angularBasis i) (P.curveDerivative b t))
    (ddf := fun t => (nativeAngularRate i^2-P.potential t)*nativePoissonCoordinate P b i t)
  · intro t ht
    exact (innerSL ℝ (angularBasis i)).hasFDerivAt.comp_hasDerivWithinAt t
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt P.κ_nonneg P.κ_lt_one
        P.potential P.kernel_bound P.nonneg b t ht)
  · exact P.coordinate_second_right_jet b i
  · exact ((continuous_const.sub P.potential.continuous).mul
      (P.coordinate_continuous b i)).continuousOn

theorem NativeHighPotential.entranceExtension_jets (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) (t : ℝ) (ht : 0 ≤ t) :
    nativePoissonEntranceExtension P b i t = nativePoissonCoordinate P b i t ∧
    deriv (nativePoissonEntranceExtension P b i) t =
      inner ℝ (angularBasis i) (P.curveDerivative b t) ∧
    deriv (deriv (nativePoissonEntranceExtension P b i)) t =
      (nativeAngularRate i^2-P.potential t)*nativePoissonCoordinate P b i t := by
  apply halfLineC2Extension_jets
  · intro s hs
    exact (innerSL ℝ (angularBasis i)).hasFDerivAt.comp_hasDerivWithinAt s
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt P.κ_nonneg P.κ_lt_one
        P.potential P.kernel_bound P.nonneg b s hs)
  · exact P.coordinate_second_right_jet b i
  · exact ht

#print axioms NativeHighPotential.coordinate_second_right_jet
#print axioms NativeHighPotential.entranceExtension_C2
#print axioms NativeHighPotential.entranceExtension_jets
end Yamabe3.Analysis.Delaunay
