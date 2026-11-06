import Yamabe3.Analysis.Cylinder.NativeHalfEndGlobalProjection
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence

/-!
# The actual forced inverse as a physical L2 continuous linear map

Joint representatives are genuinely selected from the original continuous
native angular curve.  The exact polar identity proves that their
physical L2 classes are independent of that selection.  Linearity is then
proved for these actual classes using the original native Dirichlet map.
The global physical square-integral estimate supplies continuity.

This is an L2-valued realization of the already constructed inverse. It
does not assert global Euclidean H1, conormal matching, or the coupled
manifold inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

/-- Genuine slice equality, with jointly measurable representatives,
gives equality of their physical functions almost everywhere. -/
theorem native_halfEnd_lift_ae_eq_of_joint_slices
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (fun θ => z (t, θ))) :
    cylinderLift w =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})]
      cylinderLift z := by
  have hzero (t : ℝ) : (fun θ => w (t, θ) - z (t, θ)) =ᵐ[angularVolume]
      ((0 : AngularL2) : S → ℝ) := by
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_zero ℝ 2 (angularVolume.restrict univ))
    filter_upwards [hae t, hc] with θ hθ hc
    rw [hθ, sub_self]
    exact (hc (mem_univ θ)).symm
  have htime : IntegrableOn (fun t : ℝ => Real.exp (-2 * t) * ‖(0 : AngularL2)‖ ^ 2)
      (Ioi 0) := by simp
  obtain ⟨hm, hi⟩ := native_halfEnd_lift_memLp_of_weighted_integrable
    (hw.sub hz) hzero htime
  change (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
    cylinderLift (fun p => w p - z p) x ^ 2) = _ at hi
  have hzint : (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      cylinderLift (fun p => w p - z p) x ^ 2) = 0 := by simpa using hi
  have hs := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg
    (cylinderLift (fun p => w p - z p) x)) hm.integrable_sq).mp hzint
  rw [cylinderLift_sub] at hs
  filter_upwards [hs] with x hx
  have hsq : (cylinderLift w x - cylinderLift z x) ^ 2 = 0 := hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

private theorem cylinderLift_add_values (w z : ℝ × S → ℝ) :
    cylinderLift (fun p => w p + z p) = fun x => cylinderLift w x + cylinderLift z x := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp only [cylinderLift_zero, add_zero]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    change cylinderLift (fun p => w p + z p) (y : E) =
      cylinderLift w (y : E) + cylinderLift z (y : E)
    simp only [cylinderLift_coe, puncturedCylinderLift, mul_add]

private theorem cylinderLift_const_smul_values (c : ℝ) (w : ℝ × S → ℝ) :
    cylinderLift (fun p => c * w p) = fun x => c * cylinderLift w x := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp only [cylinderLift_zero, mul_zero]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    change cylinderLift (fun p => c * w p) (y : E) = c * cylinderLift w (y : E)
    simp only [cylinderLift_coe, puncturedCylinderLift]
    ring

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- One actual joint representative of the original physical angular
curve, selected before passing to its physical L2 class. -/
def nativeHalfHighDirichletJoint (F : ℝ≥0 →ᵇ AngularL2) : ℝ × S → ℝ :=
  Classical.choose (exists_joint_L2_representative_of_continuous
    (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F))

theorem nativeHalfHighDirichletJoint_measurable (F : ℝ≥0 →ᵇ AngularL2) :
    Measurable (nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F) :=
  (Classical.choose_spec (exists_joint_L2_representative_of_continuous
    (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F))).1.measurable

theorem nativeHalfHighDirichletJoint_ae (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    (fun θ => nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) := by
  simpa only [nativeHalfHighDirichletJoint, Measure.restrict_univ] using
    (Classical.choose_spec (exists_joint_L2_representative_of_continuous
      (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F))).2 t

theorem nativeHalfHighDirichletJoint_lift_memLp (F : ℝ≥0 →ᵇ AngularL2) :
    MemLp (cylinderLift (nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F)) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) :=
  (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F
    (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 F)).1

/-- The original physical function, in its actual L2 quotient. -/
def nativeHalfHighDirichletPhysicalLp (F : ℝ≥0 →ᵇ AngularL2) :
    Lp ℝ 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) :=
  (nativeHalfHighDirichletJoint_lift_memLp hκ0 hκ1 V hV hV0 F).toLp
    (cylinderLift (nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F))

/-- Any actual joint representative of the same original native curve
produces exactly the constructed physical L2 class. -/
theorem nativeHalfHighDirichletPhysicalLp_eq_toLp
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F =
      (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE).1.toLp
        (cylinderLift w) := by
  apply MemLp.toLp_congr
  exact native_halfEnd_lift_ae_eq_of_joint_slices
    (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 F) hw
    (fun t => (nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 F t).trans (hwAE t).symm)

theorem nativeHalfHighDirichletPhysicalLp_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F‖ ≤
      (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖ := by
  have he := native_norm_toLp_sq_eq_integral_sq
    (nativeHalfHighDirichletJoint_lift_memLp hκ0 hκ1 V hV hV0 F)
  change ‖nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F‖ ^ 2 = _ at he
  have hb := (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F
    (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 F)).2
  rw [← he] at hb
  have hC : 0 ≤ (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖ := by positivity
  nlinarith [norm_nonneg (nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F),
    sq_nonneg ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖)]

theorem nativeHalfHighDirichletPhysicalLp_add (F G : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 (F + G) =
      nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F +
        nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 G := by
  let w := nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F
  let z := nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 G
  have hw := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 F
  have hz := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 G
  have hAE (t : ℝ) : (fun θ => w (t, θ) + z (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (F + G) t : S → ℝ) := by
    have hadd : nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (F + G) t =
        nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t +
          nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 G t := by
      simp only [nativeHalfHighDirichletPhysical, map_add,
        BoundedContinuousFunction.add_apply, smul_add]
    rw [hadd]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_add (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 G t))
    filter_upwards [nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 F t,
      nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 G t, hc] with θ hF hG hc
    change w (t, θ) + z (t, θ) = _
    dsimp only [w, z]
    rw [hF, hG]
    exact (hc (mem_univ θ)).symm
  rw [nativeHalfHighDirichletPhysicalLp_eq_toLp hκ0 hκ1 V hV hV0 (F + G)
    (w := fun p => w p + z p) (hw.add hz) hAE]
  simp only [cylinderLift_add_values]
  rfl

theorem nativeHalfHighDirichletPhysicalLp_smul (c : ℝ) (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 (c • F) =
      c • nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0 F := by
  let w := nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 F
  have hw := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 F
  have hAE (t : ℝ) : (fun θ => c * w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (c • F) t : S → ℝ) := by
    have hsmul : nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (c • F) t =
        c • nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t := by
      simp only [nativeHalfHighDirichletPhysical, map_smul,
        BoundedContinuousFunction.smul_apply, smul_comm (Real.exp (-2 * t)) c]
    rw [hsmul]
    have hc := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_smul c (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t))
    filter_upwards [nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 F t, hc] with θ hF hc
    change c * w (t, θ) = _
    dsimp only [w]
    rw [hF]
    simpa only [Pi.smul_apply, smul_eq_mul] using (hc (mem_univ θ)).symm
  rw [nativeHalfHighDirichletPhysicalLp_eq_toLp hκ0 hκ1 V hV hV0 (c • F)
    (w := fun p => c * w p) (measurable_const.mul hw) hAE]
  simp only [cylinderLift_const_smul_values]
  rfl

/-- A genuine continuous linear realization of the original forced
Dirichlet construction in physical L2 on the punctured unit ball. -/
def nativeHalfHighDirichletPhysicalCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) :=
  ({ toFun := nativeHalfHighDirichletPhysicalLp hκ0 hκ1 V hV hV0
     map_add' := nativeHalfHighDirichletPhysicalLp_add hκ0 hκ1 V hV hV0
     map_smul' := nativeHalfHighDirichletPhysicalLp_smul hκ0 hκ1 V hV hV0 } :
      (ℝ≥0 →ᵇ AngularL2) →ₗ[ℝ]
        Lp ℝ 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)}))).mkContinuous
    (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2))
    (nativeHalfHighDirichletPhysicalLp_norm_le hκ0 hκ1 V hV hV0)

#print axioms native_halfEnd_lift_ae_eq_of_joint_slices
#print axioms nativeHalfHighDirichletPhysicalLp_eq_toLp
#print axioms nativeHalfHighDirichletPhysicalLp_norm_le
#print axioms nativeHalfHighDirichletPhysicalLp_add
#print axioms nativeHalfHighDirichletPhysicalLp_smul
#print axioms nativeHalfHighDirichletPhysicalCLM

end Yamabe3.Analysis.SpherePolar
