import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! Genuine polar L2 transport for strongly measurable angular source
classes. Time-almost-everywhere slice equality is sufficient. The actual
logarithmic polar measure identity is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem native_slice_square_eq {u : AngularL2} {w : S → ℝ}
    (hae : w=ᵐ[angularVolume] (u : S → ℝ)) :
    (∫ θ : S,w θ^2 ∂angularVolume)=‖u‖^2 := by
  have h := joint_L2_integral_sq (U := fun _ : ℝ => u) (w := fun p : ℝ × S => w p.2)
    (fun _ => ae_restrict_of_ae (s := univ) hae) 0
  simpa only [Measure.restrict_univ] using h

theorem native_joint_memLp_interval_of_memLp {U : ℝ → AngularL2} (hU : MemLp U 2)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    MemLp w 2 ((volume.restrict (Icc a b)).prod angularVolume) := by
  apply (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hw.pow_const 2).aestronglyMeasurable).mpr
  have hae' := ae_restrict_of_ae (s := Icc a b) hae
  constructor
  · filter_upwards [hae'] with t ht
    have hu : MemLp (U t : S → ℝ) 2 angularVolume := by
      simpa only [Measure.restrict_univ] using Lp.memLp (U t)
    exact (hu.ae_eq ht.symm).integrable_sq
  · have he : (fun t => ∫ θ : S,‖w (t,θ)^2‖ ∂angularVolume)=ᵐ[volume.restrict (Icc a b)]
        (fun t => ‖U t‖^2) := by
      filter_upwards [hae'] with t ht
      simp only [Real.norm_of_nonneg (sq_nonneg _)]
      exact native_slice_square_eq ht
    exact ((memLp_two_iff_integrable_sq_norm hU.1).mp hU).integrableOn.congr he.symm

theorem native_joint_shell_square (a b : ℝ) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hprod : MemLp w 2 ((volume.restrict (Icc a b)).prod angularVolume)) :
    (∫ x in cylinderShell a b, cylinderLift w x ^ 2) =
      ∫ t in Icc a b, Real.exp (-2 * t) * (∫ θ : S,w (t,θ)^2 ∂angularVolume) := by
  have hL2 := memLp_cylinderLift_on_shell hw a b
    hprod
  have hm : Measurable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) :=
    ((measurable_cylinderLift hw).pow_const 2).indicator (measurableSet_cylinderShell a b)
  have hi : Integrable ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) :=
    (integrable_indicator_iff (measurableSet_cylinderShell a b)).mpr hL2.integrable_sq
  have hinner (t : ℝ) :
      (∫ θ : S, (Icc a b ×ˢ (univ : Set S)).indicator
        (fun p : ℝ × S => Real.exp (-2 * p.1) * w p ^ 2) (t, θ) ∂angularVolume) =
        (Icc a b).indicator (fun s : ℝ => Real.exp (-2 * s) * (∫ θ : S,w (s,θ)^2 ∂angularVolume)) t := by
    by_cases ht : t ∈ Icc a b
    · rw [Set.indicator_of_mem ht]
      calc
        _ = ∫ θ : S, Real.exp (-2 * t) * w (t, θ) ^ 2 ∂angularVolume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun θ => Set.indicator_of_mem
            (show (t, θ) ∈ Icc a b ×ˢ (univ : Set S) from ⟨ht, mem_univ θ⟩) _
        _ = _ := by rw [integral_const_mul]
    · rw [Set.indicator_of_notMem ht]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun θ =>
        Set.indicator_of_notMem (fun h => ht h.1) _
  calc
    _ = ∫ x : E, (cylinderShell a b).indicator (fun y : E => cylinderLift w y ^ 2) x :=
      (integral_indicator (measurableSet_cylinderShell a b)).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight
        ((cylinderShell a b).indicator (fun x : E => cylinderLift w x ^ 2)) (t, θ)
          ∂angularVolume := integral_euclidean_eq_cylinder hm hi
    _ = ∫ t : ℝ, (Icc a b).indicator
        (fun s : ℝ => Real.exp (-2 * s) * (∫ θ : S,w (s,θ)^2 ∂angularVolume)) t := by
      simp_rw [logCylinderWeight_shell_square, hinner]
    _ = _ := integral_indicator measurableSet_Icc


theorem native_L2_shell_square {U : ℝ → AngularL2} (hU : MemLp U 2)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) (a b : ℝ) :
    (∫ x in cylinderShell a b,cylinderLift w x^2)=
      ∫ t in Icc a b,Real.exp (-2*t)*‖U t‖^2 := by
  rw [native_joint_shell_square a b hw (native_joint_memLp_interval_of_memLp hU hw hae a b)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Icc a b) hae] with t ht
  rw [native_slice_square_eq ht]

theorem native_shell_lift_ae_eq_of_ae_slices {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hae : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ))=ᵐ[angularVolume] (fun θ => z (t,θ))) (a b : ℝ) :
    cylinderLift w=ᵐ[volume.restrict (cylinderShell a b)] cylinderLift z := by
  have hzero : ∀ᵐ t : ℝ ∂volume,(fun θ => w (t,θ)-z (t,θ))=ᵐ[angularVolume] ((0:AngularL2) : S → ℝ) := by
    filter_upwards [hae] with t ht
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_zero ℝ 2 (angularVolume.restrict univ))
    filter_upwards [ht,hc] with θ hθ hc
    rw [hθ,sub_self]
    exact (hc (mem_univ θ)).symm
  have hm := memLp_cylinderLift_on_shell (hw.sub hz) a b
    (native_joint_memLp_interval_of_memLp (MemLp.zero : MemLp (fun _ : ℝ => (0:AngularL2)) 2) (hw.sub hz) hzero a b)
  have hi := native_L2_shell_square (MemLp.zero : MemLp (fun _ : ℝ => (0:AngularL2)) 2) (hw.sub hz) hzero a b
  change (∫ x in cylinderShell a b,cylinderLift (fun p => w p-z p) x^2)=_ at hi
  have hzint : (∫ x in cylinderShell a b,cylinderLift (fun p => w p-z p) x^2)=0 := by simpa using hi
  have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg
    (cylinderLift (fun p => w p-z p) x)) hm.integrable_sq).mp hzint
  rw [cylinderLift_sub] at hs
  filter_upwards [hs] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

#print axioms native_slice_square_eq
#print axioms native_joint_memLp_interval_of_memLp
#print axioms native_joint_shell_square
#print axioms native_L2_shell_square
#print axioms native_shell_lift_ae_eq_of_ae_slices
end Yamabe3.Analysis.SpherePolar
