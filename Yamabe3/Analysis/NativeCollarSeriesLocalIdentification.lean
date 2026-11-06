import Yamabe3.Analysis.NativeC2CollarSeries
import Yamabe3.Analysis.L2JointRepresentative
import Yamabe3.Analysis.Cylinder.NativeContinuousAngularFilterApproximation
import Yamabe3.Analysis.Cylinder.NativeAngularPhysicalH1

/-! Identification of a strongly convergent actual physical-mode sum
with the lift of the same continuous angular curve on the actual collar.
The finite identity is required only on that collar, so a tail calculation
does not impose an artificial negative-time PDE. The argument compares
two L2 limits and never restricts a volume a.e. equality to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem nativeCollarSeries_eq_lift_on_collar (u : AngularIndex → E → ℝ)
    (hu : ∀ i,ContDiffOn ℝ 2 (u i) ({0}ᶜ : Set E))
    (hsum : Summable (fun i => nativeC2CollarValue (hu i)))
    (U : ℝ → AngularL2) (hU : Continuous U)
    (hfinite : ∀ (s : Finset AngularIndex) (x : E),x∈nativePoissonEntranceCollar →
      cylinderLift (projectedAngular s U) x=∑ i ∈ s,u i x)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ)) =ᵐ[angularVolume] (U t : S → ℝ)) :
    (⇑(∑' i,nativeC2CollarValue (hu i)))=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  classical
  let : Countable AngularIndex := countable_angularIndex
  let V := nativePoissonEntranceCollar
  let K := cylinderShell (-(1/2:ℝ)) (1/2)
  have hVK : V ⊆ K := by
    intro x hx
    have h := (nativePolarTimeWindow_norm (1/2) x).mp hx
    exact ⟨h.1.le,by simpa only [neg_neg] using h.2.le⟩
  have hwK := memLp_continuous_angular_lift hU hw hae (-(1/2:ℝ)) (1/2)
  have hwV := hwK.mono_measure (Measure.restrict_mono hVK le_rfl)
  have hsK (s : Finset AngularIndex) := memLp_projectedAngular_lift_of_continuous s hU (-(1/2:ℝ)) (1/2)
  have hsV (s : Finset AngularIndex) := (hsK s).mono_measure (Measure.restrict_mono hVK le_rfl)
  have herr := integral_projectedAngular_lift_error_tendsto_filter
    (tendsto_id : Tendsto (id : Finset AngularIndex → Finset AngularIndex) atTop atTop) hU hw hae (-(1/2:ℝ)) (1/2)
  have herrV := native_tendsto_integral_sq_sub_restrict hVK hsK hwK herr
  have hlim := native_tendsto_toLp_of_integral_sq_sub_filter hsV hwV herrV
  have he (s : Finset AngularIndex) :
      (∑ i ∈ s,nativeC2CollarValue (hu i))=(hsV s).toLp (cylinderLift (projectedAngular s U)) := by
    have hsm := memLp_finsetSum s (fun i _ => (nativeC2Collar_memLp (hu i)).1)
    change (∑ i ∈ s,(nativeC2Collar_memLp (hu i)).1.toLp (u i))=_
    rw [lp_finset_sum_toLp _ _ s hsm]
    apply Lp.ext
    filter_upwards [hsm.coeFn_toLp,(hsV s).coeFn_toLp,ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hy hxm
    rw [hx,hy,hfinite s x hxm]
  have hlim' : Tendsto (fun s : Finset AngularIndex => ∑ i ∈ s,nativeC2CollarValue (hu i))
      atTop (𝓝 (hwV.toLp (cylinderLift w))) :=
    hlim.congr' (Eventually.of_forall fun s => (he s).symm)
  have heq : (∑' i,nativeC2CollarValue (hu i))=hwV.toLp (cylinderLift w) :=
    tendsto_nhds_unique hsum.hasSum hlim'
  rw [heq]
  exact hwV.coeFn_toLp

#print axioms nativeCollarSeries_eq_lift_on_collar
end Yamabe3.Analysis.SpherePolar
