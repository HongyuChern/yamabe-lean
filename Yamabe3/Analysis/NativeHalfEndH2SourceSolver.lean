import Yamabe3.Analysis.NativeHalfEndSourceRegularity
import Yamabe3.Analysis.NativeHalfEndH4Regularity
import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalL2Operator
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndZeroBoundary
import Yamabe3.Analysis.NativeForcedHalfEndRadialTrace

/-!
# The physical high H2 source graph drives the same zero-entrance half-end

The source curve, its norm bound and its physical H2 regularity are now
constructed from the source graph.  The same previously built Dirichlet
solution has the genuine zero entrance, MemH01 and interior local H4.
This is an L2-bounded solver with local H4, not yet an H4-graph bounded
solver: a uniform boundary/collar estimate is still required.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Elliptic

/-- Kernel of the actual low-mode defect, on the original source graph. -/
def halfEndH2HighSourceDefect : HalfEndPhysicalH2SourceGraph →L[ℝ] (ℝ≥0 →ᵇ AngularL2) :=
  ((nativeHighProjection.compLeftContinuousBounded ℝ≥0) -
    ContinuousLinearMap.id ℝ (ℝ≥0 →ᵇ AngularL2)).comp halfEndH2SourceToAngularCLM

abbrev HalfEndHighH2Source : Type := ↥halfEndH2HighSourceDefect.ker

instance halfEndHighH2Source_completeSpace : CompleteSpace HalfEndHighH2Source :=
  halfEndH2HighSourceDefect.isClosed_ker.completeSpace_coe

theorem halfEndHighH2Source_high (f : HalfEndHighH2Source) (t : ℝ≥0) :
    nativeHighProjection (halfEndH2SourceToAngularCLM f.1 t) =
      halfEndH2SourceToAngularCLM f.1 t := by
  have h := congrArg (fun G : ℝ≥0 →ᵇ AngularL2 => G t) f.2
  change nativeHighProjection (halfEndH2SourceToAngularCLM f.1 t) -
    halfEndH2SourceToAngularCLM f.1 t = 0 at h
  exact sub_eq_zero.mp h

theorem halfEndSourceCylinderCLM_toNNReal (f : HalfEndSourceValue) (t : ℝ) (θ : S) :
    halfEndSourceCylinderCLM f ((t.toNNReal : ℝ), θ) = halfEndSourceCylinderCLM f (t, θ) := by
  change -f (halfEndSourceCylinderPoint ((t.toNNReal : ℝ), θ)) =
    -f (halfEndSourceCylinderPoint (t, θ))
  congr 2
  apply Subtype.ext
  change Real.exp (-max (t.toNNReal : ℝ) 0) • (θ : E) = Real.exp (-max t 0) • (θ : E)
  simp only [Real.coe_toNNReal', max_assoc, max_self]

theorem halfEndHighH2Source_representative_ae (f : HalfEndHighH2Source) (t : ℝ) :
    (fun θ => halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1) (t, θ))
      =ᵐ[angularVolume] (nativeHighProjection (halfEndH2SourceToAngularCLM f.1 t.toNNReal) : S → ℝ) := by
  rw [halfEndHighH2Source_high]
  have h := cylinderTestL2_ae
    (halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1))
    (halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1)).continuous
    (t.toNNReal : ℝ)
  apply EventuallyEq.trans (Eventually.of_forall fun θ =>
    (halfEndSourceCylinderCLM_toNNReal _ t θ).symm) h.symm

theorem halfEndH2SourceToAngularCLM_norm_le (f : HalfEndPhysicalH2SourceGraph) :
    ‖halfEndH2SourceToAngularCLM f‖ ≤ ‖nativeSphereL2Inclusion‖ * ‖f‖ := by
  exact (halfEndSourceToAngularCLM_norm_le _).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le f.1) (norm_nonneg nativeSphereL2Inclusion))

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The same actual source graph, through the proved signed source map,
feeds the actual Dirichlet inverse.  Only the L2 operator norm is claimed. -/
def nativeHalfEndH2SourcePhysicalL2CLM : HalfEndHighH2Source →L[ℝ]
    Lp ℝ 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) :=
  (nativeHalfHighDirichletPhysicalCLM hκ0 hκ1 V hV hV0).comp
    (halfEndH2SourceToAngularCLM.comp halfEndH2HighSourceDefect.ker.subtypeL)

def nativeHalfEndH2SourceJoint (f : HalfEndHighH2Source) : ℝ × S → ℝ :=
  nativeHalfHighDirichletJoint hκ0 hκ1 V hV hV0 (halfEndH2SourceToAngularCLM f.1)

theorem nativeHalfEndH2SourcePhysicalL2CLM_norm_le (f : HalfEndHighH2Source) :
    ‖nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 V hV hV0 f‖ ≤
      (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) *
        ‖nativeSphereL2Inclusion‖ * ‖f.1‖ := by
  have h := nativeHalfHighDirichletPhysicalLp_norm_le hκ0 hκ1 V hV hV0
    (halfEndH2SourceToAngularCLM f.1)
  change ‖nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 V hV hV0 f‖ ≤ _ at h
  exact h.trans ((mul_le_mul_of_nonneg_left (halfEndH2SourceToAngularCLM_norm_le f.1)
    (by positivity)).trans_eq (by simp only [mul_assoc]))

/-- Interior H4 is proved for the one chosen joint representative.  The
source's local H2 assumption is discharged by the original source graph. -/
theorem nativeHalfEndH2SourceJoint_local_H4
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) (f : HalfEndHighH2Source) :
    MemWkpLocally 4 (cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  let w := nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f
  let z := halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f.1)
  have hw : Measurable w := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0 _
  have hz : Measurable (fun p => z p) := z.continuous.measurable
  have hwAE := nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0 (halfEndH2SourceToAngularCLM f.1)
  have hzAE := halfEndHighH2Source_representative_ae f
  have hf2 := halfEndH2SourceGraph_forcing_local_H2 f.1
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx.2
  have hxn : ‖x‖ < 1 := by simpa using hx.1
  let t := -Real.log ‖x‖
  have ht : 0 < t := neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hx0) hxn)
  have hxA : x ∈ cylinderAnnulus (t / 2) (t + 1) :=
    mem_cylinderAnnulus_of_log_norm hx0 (by change t / 2 < t; linarith)
      (by change t < t + 1; linarith)
  have hAO : cylinderAnnulus (t / 2) (t + 1) ⊆ Metric.ball (0 : E) 1 \ {(0 : E)} :=
    subset_closure.trans (closure_positive_cylinderAnnulus_subset_halfEnd (by linarith))
  obtain ⟨W, hW, hxW, hWA, hreg⟩ := native_forced_halfEnd_local_H4_on_annulus
    hκ0 hκ1 V hV hV0 hVs (halfEndH2SourceToAngularCLM f.1) hw hz hwAE hzAE
    (a := t / 2) (b := t + 1) (by linarith)
    (hf2.restrict (isOpen_cylinderAnnulus _ _) hAO) x hxA
  exact ⟨W, hW, hxW, hWA.trans hAO, hreg⟩

/-- A single solution has the original zero-entrance trace, its physical
L2 class, MemH01 and local H4.  This does not supply the missing uniform
H4 boundary/collar estimate. -/
theorem nativeHalfEndH2Source_same_solution
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) (f : HalfEndHighH2Source) :
    let w := nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f
    Measurable w ∧
    (nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 V hV hV0 f : E → ℝ)
      =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})] cylinderLift w ∧
    MemH01 (cylinderLift w) (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    MemWkpLocally 4 (cylinderLift w) (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 (halfEndH2SourceToAngularCLM f.1) 1 = 0 ∧
    HasDerivWithinAt
      (nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 (halfEndH2SourceToAngularCLM f.1))
      (-(nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0
        (halfEndH2SourceToAngularCLM f.1))) (Ioc 0 1) 1 := by
  have hw := nativeHalfHighDirichletJoint_measurable hκ0 hκ1 V hV hV0
    (halfEndH2SourceToAngularCLM f.1)
  have hwAE := nativeHalfHighDirichletJoint_ae hκ0 hκ1 V hV hV0
    (halfEndH2SourceToAngularCLM f.1)
  refine ⟨hw, ?_, native_forced_halfEnd_memH01 hκ0 hκ1 V hV hV0 _ hw hwAE,
    nativeHalfEndH2SourceJoint_local_H4 hκ0 hκ1 V hV hV0 hVs f,
    nativeHalfHighDirichletRadial_one hκ0 hκ1 V hV hV0 _,
    nativeHalfHighDirichletRadial_hasDerivWithinAt_one hκ0 hκ1 V hV hV0 _⟩
  exact (nativeHalfHighDirichletJoint_lift_memLp hκ0 hκ1 V hV hV0
    (halfEndH2SourceToAngularCLM f.1)).coeFn_toLp

#print axioms nativeHalfEndH2SourceJoint_local_H4
#print axioms nativeHalfEndH2Source_same_solution

end Yamabe3.Analysis.UniformElliptic
