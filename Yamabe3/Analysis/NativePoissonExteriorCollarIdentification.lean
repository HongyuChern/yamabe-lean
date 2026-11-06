import Yamabe3.Analysis.NativePoissonExteriorCurve

/-! The H2 collar value is the lift of a genuine joint representative of
the original reversed-time exterior Poisson curve, with the same boundary datum.
The representative is produced once; no derivative limit is changed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativePoissonExteriorCollarValue_eq_lift (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ)) =ᵐ[angularVolume] (nativePoissonExteriorCurve P b t : S → ℝ)) :
    (nativePoissonExteriorCollarValue P b : E → ℝ) =ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  classical
  let : Countable AngularIndex := countable_angularIndex
  let V := nativePoissonEntranceCollar
  let K := cylinderShell (-(1/2:ℝ)) (1/2)
  have hVK : V ⊆ K := by
    intro x hx
    have h := (nativePolarTimeWindow_norm (1/2) x).mp hx
    exact ⟨h.1.le,by simpa only [neg_neg] using h.2.le⟩
  have hU := nativePoissonExteriorCurve_continuous P b
  have hwK := memLp_continuous_angular_lift hU hw hae (-(1/2:ℝ)) (1/2)
  have hwV := hwK.mono_measure (Measure.restrict_mono hVK le_rfl)
  have hsK (s : Finset AngularIndex) := memLp_projectedAngular_lift_of_continuous s hU (-(1/2:ℝ)) (1/2)
  have hsV (s : Finset AngularIndex) := (hsK s).mono_measure (Measure.restrict_mono hVK le_rfl)
  have herr := integral_projectedAngular_lift_error_tendsto_filter
    (tendsto_id : Tendsto (id : Finset AngularIndex → Finset AngularIndex) atTop atTop) hU hw hae (-(1/2:ℝ)) (1/2)
  have herrV := native_tendsto_integral_sq_sub_restrict hVK hsK hwK herr
  have hlim := native_tendsto_toLp_of_integral_sq_sub_filter hsV hwV herrV
  have he (s : Finset AngularIndex) :
      (∑ i ∈ s,nativePoissonExteriorCollarValueMode P b i) =
        (hsV s).toLp (cylinderLift (projectedAngular s (nativePoissonExteriorCurve P b))) := by
    have hsm := memLp_finsetSum s (fun i _ => (nativePoissonExteriorCollarMode_memLp P b i).1)
    change (∑ i ∈ s,(nativePoissonExteriorCollarMode_memLp P b i).1.toLp (nativePoissonExteriorCollarMode P b i)) = _
    rw [lp_finset_sum_toLp _ _ s hsm]
    apply Lp.ext
    filter_upwards [hsm.coeFn_toLp,(hsV s).coeFn_toLp] with x hx hy
    rw [hx,hy,nativePoissonExteriorCurve_finite_lift]
    exact congrFun (nativePoissonExteriorCollarMode_sum P b s) x
  have hlim' : Tendsto (fun s : Finset AngularIndex => ∑ i ∈ s,nativePoissonExteriorCollarValueMode P b i)
      atTop (𝓝 (hwV.toLp (cylinderLift w))) := by
    exact hlim.congr' (Eventually.of_forall fun s => (he s).symm)
  have hsum := (nativePoissonExteriorCollar_modes_summable P b hb).1.hasSum
  have heq : nativePoissonExteriorCollarValue P b = hwV.toLp (cylinderLift w) := tendsto_nhds_unique hsum hlim'
  rw [heq]
  exact hwV.coeFn_toLp

theorem exists_nativePoissonExterior_same_curve_H2_collar (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,t ≤ 0 → (fun θ => w (t,θ)) =ᵐ[angularVolume] (P.curve b (-t) : S → ℝ)) ∧
      (nativePoissonExteriorCollarValue P b : E → ℝ) =ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w ∧
      MemWkp 2 2 (nativePoissonExteriorCollarValue P b) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (nativePoissonExteriorCollarFirst P b j)
        (nativePoissonExteriorCollarValue P b) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (nativePoissonExteriorCollarSecond P b k j)
        (nativePoissonExteriorCollarFirst P b j) nativePoissonEntranceCollar) := by
  obtain ⟨w,hw,hall,hpos⟩ := nativePoissonExteriorCurve_joint_representative P b
  have h := nativePoissonExteriorCollar_H2_and_strong_jets P b hb
  exact ⟨w,hw,hpos,nativePoissonExteriorCollarValue_eq_lift P b hb hw.measurable hall,h.1,h.2.1,h.2.2.1⟩

#print axioms nativePoissonExteriorCollarValue_eq_lift
#print axioms exists_nativePoissonExterior_same_curve_H2_collar
end Yamabe3.Analysis.SpherePolar
