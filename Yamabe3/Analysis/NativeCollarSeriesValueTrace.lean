import Yamabe3.Analysis.NativeCollarJetLimits
import Yamabe3.Analysis.L2MeasureRestriction
import Yamabe3.Analysis.Cylinder.NativeContinuousAngularFilterApproximation

/-! The actual sphere restriction of each finite physical lift converges
to the angular entrance. Strong H2 convergence binds this entrance to the
constructed collar trace, without restricting volume-a.e. representatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeAngularTraceCLM : AngularL2 →L[ℝ] Lp ℝ 2 angularVolume :=
  l2MeasureRestrictCLM (by rw [Measure.restrict_univ])

theorem nativeAngularTraceCLM_ae (u : AngularL2) :
    (nativeAngularTraceCLM u : S → ℝ)=ᵐ[angularVolume] (u : S → ℝ) :=
  l2MeasureRestrict_ae (by rw [Measure.restrict_univ]) u

theorem nativeC2ValueTraceLinear_ae (u : nativeC2OffZero) :
    (nativeC2ValueTraceLinear u : S → ℝ)=ᵐ[angularVolume] (fun θ : S => u.val (θ:E)) :=
  (native_C1_sphere_restriction_memLp u.property.continuousOn).coeFn_toLp

theorem native_cylinderLift_sphere (w : ℝ × S → ℝ) (θ : S) : cylinderLift w (θ:E)=w (0,θ) := by
  simpa only [one_smul,Real.log_one,neg_zero,div_self (by norm_num : (2:ℝ)≠0),zero_div,
    Real.exp_zero,one_mul,radialScale,Real.rpow_neg,Real.one_rpow,inv_one] using cylinderLift_smul w (r := 1) (by norm_num) θ

theorem nativeC2ValueTrace_finite_lift (u : AngularIndex → nativeC2OffZero) (U : ℝ → AngularL2)
    (hfinite : ∀ s : Finset AngularIndex,cylinderLift (projectedAngular s U)=fun x => ∑ i ∈ s,(u i).val x)
    (s : Finset AngularIndex) :
    nativeC2ValueTraceLinear (∑ i ∈ s,u i)=nativeAngularTraceCLM (finiteHilbertProjection angularBasis s (U 0)) := by
  apply Lp.ext
  filter_upwards [nativeC2ValueTraceLinear_ae (∑ i ∈ s,u i),projectedAngular_ae s U 0,
    nativeAngularTraceCLM_ae (finiteHilbertProjection angularBasis s (U 0))] with θ ht hp hmap
  rw [ht]
  simp only [Submodule.coe_sum,Finset.sum_apply]
  rw [← congrFun (hfinite s) (θ:E),native_cylinderLift_sphere]
  exact hp.trans hmap.symm

theorem nativeCollarSeries_value_trace (u : AngularIndex → nativeC2OffZero) (U : ℝ → AngularL2)
    (hv : Summable (fun i => nativeC2CollarValue (u i).property))
    (hp : ∀ j,Summable (fun i => nativeC2CollarFirst (u i).property j))
    (hs : ∀ k j,Summable (fun i => nativeC2CollarSecond (u i).property k j))
    (hfinite : ∀ s : Finset AngularIndex,cylinderLift (projectedAngular s U)=fun x => ∑ i ∈ s,(u i).val x)
    (J : nativeCollarJetClosure)
    (hJ : J.val=((∑' i,nativeC2CollarValue (u i).property),
      (fun j => ∑' i,nativeC2CollarFirst (u i).property j),
      (fun k j => ∑' i,nativeC2CollarSecond (u i).property k j))) :
    nativeCollarValueTraceCLM J=nativeAngularTraceCLM (U 0) := by
  apply nativeCollarValueTrace_of_C2_limit (l := atTop) (fun s : Finset AngularIndex => ∑ i ∈ s,u i) J
  · rw [hJ]
    exact nativeC2CollarJet_series_tendsto u hv hp hs
  · have h := nativeAngularTraceCLM.continuous.continuousAt.tendsto.comp
      (finiteHilbertProjection_tendsto_filter angularBasis tendsto_id (U 0))
    apply h.congr'
    exact Eventually.of_forall fun s => (nativeC2ValueTrace_finite_lift u U hfinite s).symm

#print axioms native_cylinderLift_sphere
#print axioms nativeC2ValueTrace_finite_lift
#print axioms nativeCollarSeries_value_trace
end Yamabe3.Analysis.SpherePolar
