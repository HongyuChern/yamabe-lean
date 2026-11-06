import Yamabe3.Analysis.NativePhysicalSourceDuality

/-! The full time-L2 source has an actual physical L2 representative
inside the unit ball. The positive-time Jacobian weight is at most one. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem logCylinderWeight_ball_square (w : ℝ × S → ℝ) :
    logCylinderWeight ((Metric.ball 0 1 \ {(0:E)}).indicator (fun x => cylinderLift w x^2))=
      (Ioi (0:ℝ) ×ˢ (univ : Set S)).indicator (fun p => Real.exp (-2*p.1)*w p^2) := by
  funext p
  have hp := cylinderPoint_mem_punctured_unit_ball_iff p
  by_cases ht : 0<p.1
  · change Real.exp (-3*p.1)*((Metric.ball 0 1 \ {(0:E)}).indicator (fun x => cylinderLift w x^2) (cylinderPoint p))=_
    rw [indicator_of_mem (hp.mpr ht),indicator_of_mem (show p∈Ioi (0:ℝ) ×ˢ (univ : Set S) from ⟨ht,mem_univ _⟩)]
    change Real.exp (-3*p.1)*cylinderLift w (Real.exp (-p.1) • (p.2:E))^2=_
    rw [cylinderLift_smul w (Real.exp_pos _) p.2,Real.log_exp,neg_neg,mul_pow,radialScale_exp_neg]
    rw [←mul_assoc,pow_two,←Real.exp_add,←Real.exp_add]
    congr 2
    ring
  · change Real.exp (-3*p.1)*((Metric.ball 0 1 \ {(0:E)}).indicator (fun x => cylinderLift w x^2) (cylinderPoint p))=_
    rw [indicator_of_notMem (fun hx => ht (hp.mp hx)),indicator_of_notMem (show p∉Ioi (0:ℝ) ×ˢ (univ : Set S) from fun h => ht h.1),mul_zero]

theorem nativeFullPhysicalSource_memLp (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    MemLp (nativeFullPhysicalSourceRepresentative F) 2
      (volume.restrict (Metric.ball 0 1 \ {(0:E)})) := by
  let w := nativeAngularL2Joint (nativeL2FullAngularCLM F)
  have hw := nativeAngularL2Joint_measurable (nativeL2FullAngularCLM F)
  have hm := native_joint_memLp_of_memLp (Lp.memLp (nativeL2FullAngularCLM F)) hw
    (Eventually.of_forall (nativeAngularL2Joint_ae (nativeL2FullAngularCLM F)))
  have hO : MeasurableSet (Metric.ball 0 1 \ {(0:E)}) := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hI : MeasurableSet (Ioi (0:ℝ) ×ˢ (univ : Set S)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hweight : IntegrableOn (fun p : ℝ × S => Real.exp (-2*p.1)*w p^2)
      (Ioi (0:ℝ) ×ˢ (univ : Set S)) (volume.prod angularVolume) := by
    apply hm.integrable_sq.integrableOn.bdd_mul (c := 1) (by fun_prop)
    filter_upwards [ae_restrict_mem hI] with p hp
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith [show 0 < p.1 from hp.1])
  have he : Integrable ((Metric.ball 0 1 \ {(0:E)}).indicator (fun x => cylinderLift w x^2)) := by
    apply (integrable_euclidean_iff_cylinder (((measurable_cylinderLift hw).pow_const 2).indicator hO)).mpr
    rw [logCylinderWeight_ball_square]
    exact (integrable_indicator_iff hI).mpr hweight
  exact (memLp_two_iff_integrable_sq (measurable_cylinderLift hw).aestronglyMeasurable).mpr
    ((integrable_indicator_iff hO).mp he)

#print axioms logCylinderWeight_ball_square
#print axioms nativeFullPhysicalSource_memLp
end Yamabe3.Analysis.SpherePolar
