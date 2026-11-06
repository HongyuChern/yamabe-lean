import Yamabe3.Analysis.Cylinder.NativeLogPolarIntegrals
import Yamabe3.Analysis.Cylinder.NativeCylinderTest
import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalForcing
import Yamabe3.Analysis.Sphere.NativeSphereSpectralBasis
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation
import Yamabe3.Analysis.CompactContinuousCurve
import Yamabe3.Analysis.Cylinder.NativeCylinderLift
import PoincareLib.Geometry.Manifold.ContDiff.TimeDerivative
import Yamabe3.Analysis.Cylinder.NativeCylinderConjugation
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean
import Yamabe3.Analysis.HalfEndHilbertGreen
import Yamabe3.Analysis.NativeForcedHalfEndDerivativeOperator
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralCompactness
import Yamabe3.Analysis.Cylinder.NativeHalfEndCompactTesting

/-!
# W1: original half-end physical Green formula

Seven pending proof units are preserved verbatim below. Each has its own
outer scope and explicitly closed original noncomputable section.
The earlier module paths are compatibility imports. No passed module,
physical datum, source term, metric, or theorem hypothesis is altered.
-/

-- Original proof unit: Yamabe3.Analysis.Cylinder.NativeHalfEndLogVolume
section NativeHalfEndGreenProofUnit1

/-!
# Actual logarithmic volume of the punctured unit ball

These formulas use the actual Euclidean volume, the induced round-sphere
volume, and the proved logarithmic polar change of variables.  They do
not import a spectral solution or postulate a boundary measure.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology

namespace Yamabe3.Analysis.SpherePolar

theorem cylinderPoint_mem_punctured_unit_ball_iff (p : ℝ × S) :
    cylinderPoint p ∈ Metric.ball (0 : E) 1 \ {(0 : E)} ↔ 0 < p.1 := by
  simp only [mem_diff, Metric.mem_ball, dist_zero_right, cylinderPoint_norm,
    mem_singleton_iff, cylinderPoint_ne_zero p, not_false_eq_true, and_true]
  rw [← Real.exp_zero, Real.exp_lt_exp]
  exact neg_lt_zero

theorem logCylinderWeight_punctured_unit_ball_indicator (G : E → ℝ) :
    logCylinderWeight ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set S)).indicator (logCylinderWeight G) := by
  funext p
  have hp := cylinderPoint_mem_punctured_unit_ball_iff p
  by_cases ht : 0 < p.1
  · change Real.exp (-3 * p.1) * (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G
      (cylinderPoint p) = _
    rw [Set.indicator_of_mem (hp.mpr ht), Set.indicator_of_mem
      (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set S) from ⟨ht, mem_univ _⟩)]
    rfl
  · change Real.exp (-3 * p.1) * (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G
      (cylinderPoint p) = _
    rw [Set.indicator_of_notMem (fun hx => ht (hp.mp hx)), Set.indicator_of_notMem
      (show p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set S) from fun hp => ht hp.1), mul_zero]

/-- The true volume integral on the punctured unit ball, obtained from
the actual logarithmic polar integral with its exp(-3t) Jacobian. -/
theorem native_halfEnd_integral_of_log_pullback {G : E → ℝ} (hG : Measurable G)
    (hi : Integrable (logCylinderWeight G) ((volume.restrict (Ioi (0 : ℝ))).prod angularVolume)) :
    IntegrableOn G (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, G x) =
        ∫ t in Ioi (0 : ℝ), ∫ θ : S, logCylinderWeight G (t, θ) ∂angularVolume := by
  have hO : MeasurableSet (Metric.ball (0 : E) 1 \ {(0 : E)}) :=
    (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hI : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set S)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmeasure : (volume.restrict (Ioi (0 : ℝ))).prod angularVolume =
      (volume.prod angularVolume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set S)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeasure] at hi
  have hind := (integrable_indicator_iff hI).mpr hi
  have hm : Measurable ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G) := hG.indicator hO
  have hphysical : Integrable ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G) := by
    apply (integrable_euclidean_iff_cylinder hm).mpr
    rw [logCylinderWeight_punctured_unit_ball_indicator]
    exact hind
  have hinner (t : ℝ) : (∫ θ : S,
      (Ioi (0 : ℝ) ×ˢ (univ : Set S)).indicator (logCylinderWeight G) (t, θ) ∂angularVolume) =
      (Ioi (0 : ℝ)).indicator (fun a => ∫ θ : S, logCylinderWeight G (a, θ) ∂angularVolume) t := by
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      apply integral_congr_ae
      exact Eventually.of_forall fun θ => Set.indicator_of_mem
        (show (t, θ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set S) from ⟨ht, mem_univ _⟩) _
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun θ => Set.indicator_of_notMem
        (show (t, θ) ∉ Ioi (0 : ℝ) ×ˢ (univ : Set S) from fun hp => ht hp.1) _
  refine ⟨(integrable_indicator_iff hO).mp hphysical, ?_⟩
  calc
    _ = ∫ x : E, (Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G x :=
      (integral_indicator hO).symm
    _ = ∫ t : ℝ, ∫ θ : S, logCylinderWeight
        ((Metric.ball (0 : E) 1 \ {(0 : E)}).indicator G) (t, θ) ∂angularVolume :=
      integral_euclidean_eq_cylinder hm hphysical
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator
        (fun a => ∫ θ : S, logCylinderWeight G (a, θ) ∂angularVolume) t := by
      rw [logCylinderWeight_punctured_unit_ball_indicator]
      exact integral_congr_ae (Eventually.of_forall hinner)
    _ = _ := integral_indicator measurableSet_Ioi

#print axioms cylinderPoint_mem_punctured_unit_ball_iff
#print axioms logCylinderWeight_punctured_unit_ball_indicator
#print axioms native_halfEnd_integral_of_log_pullback

end Yamabe3.Analysis.SpherePolar

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit1

-- Original proof unit: Yamabe3.Analysis.Cylinder.NativeHalfEndBoundaryTransport
section NativeHalfEndGreenProofUnit2

/-!
# Actual half-ball transport for nonzero entrance tests

The domain is the actual punctured Euclidean unit ball.  Its volume
measure is pulled back by the proved logarithmic polar formula.  No
restriction of an ambient almost-everywhere identity to the boundary is
used.  The angular representatives are paired through their L2 classes.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem boundary_hasCompactSupport_separableCylinder {q : ℝ → ℝ}
    (hc : HasCompactSupport q) (Y : S → ℝ) :
    HasCompactSupport (separableCylinder q Y) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hc.isCompact.prod (isCompact_univ : IsCompact (univ : Set S)))
  intro p hp
  refine ⟨subset_tsupport q ?_, mem_univ _⟩
  intro hz
  exact hp (by simp only [separableCylinder, hz, zero_mul])

/-- Pairing of the chosen measurable slice with a genuine smooth
eigenfunction is its original Hilbert coefficient.  This is a volume
L2 pairing and does not restrict any almost-everywhere equality to a
sphere in the ambient Euclidean space. -/
theorem native_joint_angular_pairing {U : ℝ → AngularL2} {w : ℝ × S → ℝ}
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (i : AngularIndex) (t : ℝ) :
    (∫ θ : S, w (t, θ) * angularRepresentative i θ ∂angularVolume) =
      inner ℝ (angularBasis i) (U t) := by
  calc
    _ = ∫ θ : S, (U t : S → ℝ) θ * (angularBasis i : S → ℝ) θ ∂angularVolume := by
      apply integral_congr_ae
      filter_upwards [hae t, angularRepresentative_ae i] with θ hu hy
      rw [hu, hy]
    _ = _ := by
      simp only [L2.inner_def, setIntegral_univ, RCLike.inner_apply, conj_trivial]

/-- Every genuine continuous compact joint test is integrable against
the same jointly measurable continuous L2 curve.  Local L2 control,
rather than pointwise regularity of that curve, supplies this fact. -/
theorem native_joint_compact_pair_integrable
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {η : ℝ × S → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun p : ℝ × S => w p * η p) (volume.prod angularVolume) := by
  obtain ⟨C, hC⟩ := (hc.isCompact.image continuous_fst).exists_bound_of_continuousOn
    (f := fun t : ℝ => t) continuous_id.continuousOn
  let T : Set (ℝ × S) := Icc (-C) C ×ˢ univ
  have hT : MeasurableSet T := measurableSet_Icc.prod MeasurableSet.univ
  have hl : MemLp w 2 ((volume.prod angularVolume).restrict T) := by
    simpa only [T, ← Measure.prod_restrict, Measure.restrict_univ] using
      native_joint_memLp_interval hU hw hae (-C) C
  have hwi : MemLp (T.indicator w) 2 (volume.prod angularVolume) :=
    (memLp_indicator_iff_restrict hT).mpr hl
  have htest : MemLp η 2 (volume.prod angularVolume) := hη.memLp_of_hasCompactSupport hc
  have hi := hwi.integrable_mul htest
  have heq : (fun p : ℝ × S => T.indicator w p * η p) =
      (fun p : ℝ × S => w p * η p) := by
    funext p
    by_cases hp : p ∈ T
    · rw [Set.indicator_of_mem hp]
    · have hη0 : η p = 0 := by
        by_contra hn
        have hb := hC p.1 ⟨p, subset_tsupport η hn, rfl⟩
        have ha : -C ≤ p.1 ∧ p.1 ≤ C := abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
        exact hp ⟨ha, mem_univ _⟩
      simp only [hη0, mul_zero]
  exact heq ▸ hi

/-- The separated-mode specialization retains the same original L2
representative and does not assume its pointwise angular regularity. -/
theorem native_joint_compact_separable_integrable
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {q : ℝ → ℝ} (hq : Continuous q) (hc : HasCompactSupport q) (i : AngularIndex) :
    Integrable (fun p : ℝ × S => w p * separableCylinder q (angularRepresentative i) p)
      (volume.prod angularVolume) :=
  native_joint_compact_pair_integrable hU hw hae
    ((hq.comp continuous_fst).mul ((smooth_angularRepresentative i).continuous.comp continuous_snd))
    (boundary_hasCompactSupport_separableCylinder hc _)

#print axioms native_halfEnd_integral_of_log_pullback
#print axioms native_joint_angular_pairing
#print axioms native_joint_compact_pair_integrable
#print axioms native_joint_compact_separable_integrable

end Yamabe3.Analysis.SpherePolar

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit2

-- Original proof unit: Yamabe3.Analysis.Sphere.NativeSphereTestCoefficients
section NativeHalfEndGreenProofUnit3

/-!
# Genuine smooth-test coefficients of the native angular Laplacian

The smooth function and its negative native Laplacian are explicitly
realized in the real sphere-volume L2 space.  Actual compact-support Green
identity and the proved smooth representatives of the native eigenbasis
identify every coefficient.  No spectral-domain certificate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

def smoothAngularL2 (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) : AngularL2 :=
  ((hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).restrict univ).toLp f

theorem smoothAngularL2_ae (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    (smoothAngularL2 f hf : UnitSphere 2 → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure] f := by
  have h : (smoothAngularL2 f hf : UnitSphere 2 → ℝ) =ᵐ[
      (roundSphereMetric 2).volumeMeasure.restrict univ] f :=
    ((hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).restrict univ).coeFn_toLp
  filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp h] with x hx
  exact hx (mem_univ x)

def negativeLaplacianAngularL2 (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) : AngularL2 :=
  smoothAngularL2 (fun x => -(roundSphereMetric 2).leviCivitaData.laplacian f x)
    ((roundSphereMetric 2).leviCivitaData.contMDiff_laplacian hf).neg

theorem negativeLaplacianAngularL2_ae (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    (negativeLaplacianAngularL2 f hf : UnitSphere 2 → ℝ) =ᵐ[
      (roundSphereMetric 2).volumeMeasure]
      fun x => -(roundSphereMetric 2).leviCivitaData.laplacian f x :=
  smoothAngularL2_ae _ _

theorem angularBasis_negativeLaplacian_coefficient (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (i : AngularIndex) :
    inner ℝ (angularBasis i) (negativeLaplacianAngularL2 f hf) =
      angularEigenvalue i * inner ℝ (angularBasis i) (smoothAngularL2 f hf) := by
  let D := (roundSphereMetric 2).leviCivitaData
  obtain ⟨U, hU, hUae, _, hUP⟩ := exists_smooth_angular_eigenfunction i
  have hUP' : ∀ x, -D.laplacian U x = angularEigenvalue i * U x := hUP
  have hcomm : (∫ x, U x * (-D.laplacian f x) ∂(roundSphereMetric 2).volumeMeasure) =
      ∫ x, (-D.laplacian U x) * f x ∂(roundSphereMetric 2).volumeMeasure := by
    have h := congrArg (fun z : ℝ => -z)
      (integral_mul_laplacian_comm_of_compact_tests (D := D) hU hf
        (HasCompactSupport.of_compactSpace _) (HasCompactSupport.of_compactSpace _))
    calc
      _ = -(∫ x, U x * D.laplacian f x ∂(roundSphereMetric 2).volumeMeasure) := by
        simp_rw [mul_neg]
        rw [integral_neg]
      _ = -(∫ x, f x * D.laplacian U x ∂(roundSphereMetric 2).volumeMeasure) := h
      _ = _ := by
        rw [← integral_neg]
        congr 1
        funext x
        ring
  simp only [L2.inner_def, setIntegral_univ]
  calc
    _ = ∫ x, U x * (-D.laplacian f x) ∂(roundSphereMetric 2).volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [hUae, negativeLaplacianAngularL2_ae f hf] with x hx hfx
      rw [← hx, hfx]
      simp [mul_comm, D]
    _ = ∫ x, (-D.laplacian U x) * f x ∂(roundSphereMetric 2).volumeMeasure := hcomm
    _ = angularEigenvalue i * (∫ x, U x * f x ∂(roundSphereMetric 2).volumeMeasure) := by
      simp_rw [hUP', mul_assoc]
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hUae, smoothAngularL2_ae f hf] with x hx hfx
      rw [← hx, hfx]
      simp [mul_comm]

#print axioms smoothAngularL2_ae
#print axioms negativeLaplacianAngularL2_ae
#print axioms angularBasis_negativeLaplacian_coefficient

end Yamabe3.Analysis.SphereSpectrum

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit3

-- Original proof unit: Yamabe3.Analysis.NativeCylinderTestCurve
section NativeHalfEndGreenProofUnit4

/-!
# A joint native smooth cylinder test gives an actual smooth L2 curve

Partial time regularity is proved by the fixed manifold derivative theorem.
The actual compact sphere and the continuous-map Banach FTC then prove
smoothness in its genuine volume L2 space. No Hilbert-valued regularity is
an input. Compact joint support gives compact time support by projection.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff Manifold Bundle RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SpherePolar Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

def cylinderTimeDerivative (f : ℝ × S → ℝ) (z : ℝ × S) : ℝ :=
  deriv (fun t => f (t, z.2)) z.1

def cylinderTimeJet (n : ℕ) (f : ℝ × S → ℝ) : ℝ × S → ℝ :=
  (cylinderTimeDerivative^[n]) f

theorem cylinderTimeJet_succ (n : ℕ) (f : ℝ × S → ℝ) :
    cylinderTimeJet (n + 1) f = cylinderTimeDerivative (cylinderTimeJet n f) :=
  Function.iterate_succ_apply' cylinderTimeDerivative n f

theorem smooth_cylinderTimeDerivative {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (cylinderTimeDerivative f) :=
  fun z => Poincare.Manifold.contMDiffAt_deriv_time (hf z)

theorem tsupport_cylinderTimeDerivative_subset (f : ℝ × S → ℝ) :
    tsupport (cylinderTimeDerivative f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra hnot
  apply hz
  have he : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hc : Tendsto (fun s : ℝ => (s, z.2)) (𝓝 z.1) (𝓝 z) :=
    continuousAt_id.prodMk continuousAt_const
  have ht : (fun s => f (s, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := he.comp_tendsto hc
  exact ht.deriv_eq.trans (deriv_const _ _)

theorem hasCompactSupport_cylinderTimeDerivative {f : ℝ × S → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (cylinderTimeDerivative f) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_cylinderTimeDerivative_subset f)

theorem smooth_cylinderTimeJet {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (cylinderTimeJet n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [cylinderTimeJet_succ]
    exact smooth_cylinderTimeDerivative ih

theorem cylinderTimeJet_hasDerivAt {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (t : ℝ) (x : S) :
    HasDerivAt (fun s => cylinderTimeJet n f (s, x))
      (cylinderTimeJet (n + 1) f (t, x)) t := by
  rw [cylinderTimeJet_succ]
  exact ((smooth_cylinder_time_slice (smooth_cylinderTimeJet hf n) x).differentiable
    (by simp) t).hasDerivAt

def cylinderTestContinuous (f : ℝ × S → ℝ) (hf : Continuous f) (t : ℝ) : C(S, ℝ) :=
  (ContinuousMap.curry ⟨f, hf⟩) t

def cylinderTestL2 (f : ℝ × S → ℝ) (hf : Continuous f) (t : ℝ) : AngularL2 :=
  ContinuousMap.toLp 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ
    (cylinderTestContinuous f hf t)

theorem cylinderTestL2_ae (f : ℝ × S → ℝ) (hf : Continuous f) (t : ℝ) :
    (cylinderTestL2 f hf t : S → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure]
      fun x => f (t, x) := by
  have h := ContinuousMap.coeFn_toLp (p := 2) ((roundSphereMetric 2).volumeMeasure.restrict univ)
    (𝕜 := ℝ) (cylinderTestContinuous f hf t)
  change (cylinderTestL2 f hf t : S → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure.restrict univ]
    (fun x => f (t, x)) at h
  simpa only [Measure.restrict_univ] using h

theorem cylinderTestL2_eq_smoothAngularL2 {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ) :
    cylinderTestL2 f hf.continuous t =
      smoothAngularL2 (fun x => f (t, x)) (smooth_cylinder_sphere_slice hf t) := by
  apply Lp.ext
  exact ae_restrict_of_ae ((cylinderTestL2_ae f hf.continuous t).trans
    (smoothAngularL2_ae _ _).symm)

theorem contDiff_cylinderTestL2 {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiff ℝ ∞ (cylinderTestL2 f hf.continuous) := by
  exact contDiff_L2_of_pointwise_tower
    ((roundSphereMetric 2).volumeMeasure.restrict univ) (fun n => cylinderTimeJet n f)
    (fun n => (smooth_cylinderTimeJet hf n).continuous) (cylinderTimeJet_hasDerivAt hf)

theorem hasDerivAt_cylinderTestL2 {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ) :
    HasDerivAt (cylinderTestL2 f hf.continuous)
      (cylinderTestL2 (cylinderTimeDerivative f) (smooth_cylinderTimeDerivative hf).continuous t) t := by
  have hQ : Continuous (cylinderTestContinuous (cylinderTimeDerivative f)
      (smooth_cylinderTimeDerivative hf).continuous) :=
    (ContinuousMap.curry ⟨_, (smooth_cylinderTimeDerivative hf).continuous⟩).continuous
  have hd := hasDerivAt_continuousMap_curve
    (P := cylinderTestContinuous f hf.continuous) hQ
    (fun s x => by
      change HasDerivAt (fun r => f (r, x)) (cylinderTimeDerivative f (s, x)) s
      exact ((smooth_cylinder_time_slice hf x).differentiable (by simp) s).hasDerivAt) t
  exact (ContinuousMap.toLp 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ).hasFDerivAt.comp_hasDerivAt t hd

theorem deriv_cylinderTestL2 {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    deriv (cylinderTestL2 f hf.continuous) =
      cylinderTestL2 (cylinderTimeDerivative f) (smooth_cylinderTimeDerivative hf).continuous :=
  funext fun t => (hasDerivAt_cylinderTestL2 hf t).deriv

theorem second_deriv_cylinderTestL2 {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    deriv (deriv (cylinderTestL2 f hf.continuous)) =
      cylinderTestL2 (cylinderTimeDerivative (cylinderTimeDerivative f))
        (smooth_cylinderTimeDerivative (smooth_cylinderTimeDerivative hf)).continuous := by
  rw [deriv_cylinderTestL2 hf, deriv_cylinderTestL2 (smooth_cylinderTimeDerivative hf)]

theorem hasCompactSupport_cylinderTestL2 {f : ℝ × S → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    HasCompactSupport (cylinderTestL2 f hf) := by
  have hk : IsCompact (Prod.fst '' tsupport f) := hc.image continuous_fst
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hk.isClosed
  intro t ht
  by_contra hnot
  apply ht
  change ContinuousMap.toLp 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ
    (cylinderTestContinuous f hf t) = 0
  have hz : cylinderTestContinuous f hf t = 0 := by
    apply ContinuousMap.ext
    intro x
    change f (t, x) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro htx
    exact hnot ⟨(t, x), htx, rfl⟩
  rw [hz, map_zero]

end Yamabe3.Analysis.Delaunay

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit4

-- Original proof unit: Yamabe3.Analysis.NativeCylinderTestLaplacian
section NativeHalfEndGreenProofUnit5

/-!
# Joint continuity of the actual native angular test Laplacian

The already proved native polar formula expresses the angular Laplacian
through the genuine smooth punctured Euclidean lift. The time derivatives
are actual native derivatives, so joint continuity is derived from joint
smoothness of the original test, not included as an operator-domain field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff Manifold Bundle RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SpherePolar Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

theorem tsupport_sphere_laplacian_family_subset (f : ℝ × S → ℝ) :
    tsupport (fun z : ℝ × S => sphereD.laplacian (fun x => f (z.1, x)) z.2) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra hnot
  apply hz
  have he : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hc : Tendsto (fun x : S => (z.1, x)) (𝓝 z.2) (𝓝 z) :=
    continuousAt_const.prodMk continuousAt_id
  have hx : (fun x => f (z.1, x)) =ᶠ[𝓝 z.2] 0 := he.comp_tendsto hc
  exact sphereD.laplacian_eq_zero_of_notMem_tsupport
    (notMem_tsupport_iff_eventuallyEq.mpr hx)

theorem hasCompactSupport_sphere_laplacian_family {f : ℝ × S → ℝ}
    (hc : HasCompactSupport f) :
    HasCompactSupport (fun z : ℝ × S => sphereD.laplacian (fun x => f (z.1, x)) z.2) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_sphere_laplacian_family_subset f)

theorem continuous_cylinder_laplacian_lift {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun z : ℝ × S =>
      euclideanD.laplacian (cylinderLift f) (Real.exp (-z.1) • (z.2 : E))) := by
  have hopen : IsOpen (({(0 : E)} : Set E)ᶜ) := isClosed_singleton.isOpen_compl
  have hl (y : E) (hy : y ≠ 0) : ContinuousAt (euclideanD.laplacian (cylinderLift f)) y := by
    have hs := contDiffAt_cylinderLift hf hy
    have htrace : ContDiffAt ℝ ∞ (fun z : E => ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ (cylinderLift f)) z
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)) y := by
      apply ContDiffAt.sum
      intro i hi
      exact (((hs.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const).clm_apply contDiffAt_const
    apply htrace.continuousAt.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact euclideanD.laplacian_euclideanMetric (contDiffAt_cylinderLift hf hz)
  have hmap : Continuous (fun z : ℝ × S => Real.exp (-z.1) • (z.2 : E)) :=
    (Real.continuous_exp.comp continuous_fst.neg).smul (continuous_subtype_val.comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro z
  have hn : Real.exp (-z.1) • (z.2 : E) ≠ 0 := by
    intro h
    have hnorm := congrArg norm h
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_eq_of_mem_sphere, mul_one, norm_zero] at hnorm
    exact (Real.exp_ne_zero _) hnorm
  exact (hl _ hn).comp (f := fun z : ℝ × S => Real.exp (-z.1) • (z.2 : E))
    (x := z) hmap.continuousAt

theorem continuous_native_sphere_laplacian_family {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun z : ℝ × S => sphereD.laplacian (fun x => f (z.1, x)) z.2) := by
  have heq : (fun z : ℝ × S => sphereD.laplacian (fun x => f (z.1, x)) z.2) =
      fun z => (Real.exp (-z.1) ^ 2 / Real.exp (z.1 / 2)) *
        euclideanD.laplacian (cylinderLift f) (Real.exp (-z.1) • (z.2 : E)) -
        cylinderTimeDerivative (cylinderTimeDerivative f) z + f z / 4 := by
    funext z
    have h := laplacian_cylinderLift hf (Real.exp_pos (-z.1)) z.2
    simp only [Real.log_exp, neg_neg] at h
    have hs : radialScale (Real.exp (-z.1)) = Real.exp (z.1 / 2) := by
      unfold radialScale
      rw [Real.log_exp, neg_neg]
    rw [hs] at h
    change sphereD.laplacian (fun x => f (z.1, x)) z.2 =
      (Real.exp (-z.1) ^ 2 / Real.exp (z.1 / 2)) *
        euclideanD.laplacian (cylinderLift f) (Real.exp (-z.1) • (z.2 : E)) -
        deriv (deriv (fun t => f (t, z.2))) z.1 + f z / 4
    field_simp [Real.exp_ne_zero] at h ⊢
    nlinarith only [h]
  rw [heq]
  exact (((Real.continuous_exp.comp continuous_fst.neg).pow 2).div
      (Real.continuous_exp.comp (continuous_fst.div_const 2))
      (fun z => Real.exp_ne_zero _)).mul
      (continuous_cylinder_laplacian_lift hf) |>.sub
      (smooth_cylinderTimeDerivative (smooth_cylinderTimeDerivative hf)).continuous |>.add
      (hf.continuous.div_const 4)

theorem continuous_negativeLaplacian_test_curve {f : ℝ × S → ℝ}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun t => negativeLaplacianAngularL2 (fun x => f (t, x))
      (smooth_cylinder_sphere_slice hf t)) := by
  let q : ℝ × S → ℝ := fun z => -sphereD.laplacian (fun x => f (z.1, x)) z.2
  have hq : Continuous q := (continuous_native_sphere_laplacian_family hf).neg
  have heq : (fun t => negativeLaplacianAngularL2 (fun x => f (t, x))
      (smooth_cylinder_sphere_slice hf t)) = cylinderTestL2 q hq := by
    funext t
    apply Lp.ext
    have h₁ := negativeLaplacianAngularL2_ae (fun x => f (t, x))
      (smooth_cylinder_sphere_slice hf t)
    have h₂ := cylinderTestL2_ae q hq t
    exact ae_restrict_of_ae (h₁.trans h₂.symm)
  rw [heq]
  change Continuous (fun t =>
    (ContinuousMap.toLp (E := ℝ) 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ)
      ((ContinuousMap.curry ⟨q, hq⟩) t))
  exact (ContinuousMap.toLp (E := ℝ) 2 ((roundSphereMetric 2).volumeMeasure.restrict univ) ℝ).continuous.comp
    (ContinuousMap.curry ⟨q, hq⟩).continuous

end Yamabe3.Analysis.Delaunay

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit5

-- Original proof unit: Yamabe3.Analysis.NativeHalfEndJointGreen
section NativeHalfEndGreenProofUnit6

/-!
# All genuine smooth joint tests for the original forced half-end

The original solution, derivative and source are instantiated directly
in the proved half-line Hilbert Green identity.  A genuine smooth joint
cylinder function supplies its own smooth L2 test curve, actual angular
Laplacian image, and entrance value.  No test-operator graph assumption
or boundary value is imposed on that function.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Manifold ContDiff Bundle Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open Yamabe3.Analysis.SpherePolar SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

private theorem halfEnd_countable_angularIndex : Countable AngularIndex :=
  Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
    (domainL2Resolvent sphereD univ)
    (isCompactOperator_domainL2Resolvent sphereD univ (by decide) isOpen_univ
      (by simpa using (isCompact_univ : IsCompact (univ : Set S))))
    domainL2Resolvent_isSelfAdjoint

private theorem halfEnd_inner_cylinderTestL2_eq_integral
    (f : ℝ × S → ℝ) (hf : Continuous f) (t : ℝ) (U : AngularL2) :
    inner ℝ (cylinderTestL2 f hf t) U =
      ∫ θ : S, f (t, θ) * U θ ∂angularVolume := by
  simp only [L2.inner_def, setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [cylinderTestL2_ae f hf t] with θ hθ
  rw [hθ]
  simp [mul_comm]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual forced half-end satisfies all variable Hilbert tests in
the angular operator graph, with its own true entrance derivative. -/
theorem nativeHalfHighDirichlet_full_hilbert_green
    (F : ℝ≥0 →ᵇ AngularL2)
    {P AP : ℝ → AngularL2} (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P)
    (hAP : Continuous AP)
    (hA : ∀ i t, inner ℝ (angularBasis i) (AP t) =
      angularEigenvalue i * inner ℝ (angularBasis i) (P t)) :
    (∫ t in Ioi (0 : ℝ), inner ℝ (deriv (deriv P) t)
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) -
      (1 / 4) * (∫ t in Ioi (0 : ℝ), inner ℝ (P t)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) +
      (∫ t in Ioi (0 : ℝ), inner ℝ (P t)
        (V t • nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) -
      (∫ t in Ioi (0 : ℝ), inner ℝ (AP t)
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) =
      (∫ t in Ioi (0 : ℝ), inner ℝ (P t)
        (Real.exp (-2 * t) • nativeHighProjection (F t.toNNReal))) +
      inner ℝ (P 0) (nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F) := by
  letI := halfEnd_countable_angularIndex
  have hS : Continuous (fun t : ℝ => Real.exp (-2 * t) • nativeHighProjection (F t.toNNReal)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-2 * t))).smul
      (nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal))
  have hdd (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => inner ℝ (angularBasis i)
        (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F s))
        (0 * inner ℝ (angularBasis i)
          (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) +
          (angularEigenvalue i + 1 / 4) * inner ℝ (angularBasis i)
            (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) +
          inner ℝ (angularBasis i) (Real.exp (-2 * t) • nativeHighProjection (F t.toNNReal)) -
          V t * inner ℝ (angularBasis i)
            (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t)) t := by
    apply (nativeHalfHighDirichletPhysicalDerivative_coefficient_equation
      hκ0 hκ1 V hV hV0 F i t ht).congr_deriv
    rw [real_inner_smul_right]
    ring
  have h := halfEnd_hilbert_variable_green angularBasis angularEigenvalue
    (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F)
    (nativeHalfHighDirichletPhysicalDerivative_continuous hκ0 hκ1 V hV hV0 F)
    hS V.continuous
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F)
    hdd hP hcP hAP hA
  simpa only [zero_mul, add_zero, sub_zero,
    nativeHalfHighDirichletPhysical_zero_of_nonpos hκ0 hκ1 V hV hV0 F 0 le_rfl,
    inner_zero_right, nativeHalfHighDirichletEntranceDerivativeCLM_apply] using h

/-- Every actual smooth joint compact cylinder test is admissible, even
when its entrance value is nonzero.  Both its time and spherical
Laplacians are the real differential operators already constructed in
the project; the boundary term is the actual original entrance curve. -/
theorem nativeHalfHighDirichlet_original_joint_green
    (F : ℝ≥0 →ᵇ AngularL2) {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) :
    (∫ t in Ioi (0 : ℝ), ∫ θ : S,
      deriv (deriv (fun s => ψ (s, θ))) t *
        (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) θ ∂angularVolume) -
      (1 / 4) * (∫ t in Ioi (0 : ℝ), ∫ θ : S,
        ψ (t, θ) * (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) θ ∂angularVolume) +
      (∫ t in Ioi (0 : ℝ), V t * (∫ θ : S,
        ψ (t, θ) * (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) θ ∂angularVolume)) -
      (∫ t in Ioi (0 : ℝ), ∫ θ : S,
        (-sphereD.laplacian (fun «ω» => ψ (t, «ω»)) θ) *
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) θ ∂angularVolume) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * (∫ θ : S,
        ψ (t, θ) * (nativeHighProjection (F t.toNNReal) : S → ℝ) θ ∂angularVolume)) +
      inner ℝ (cylinderTestL2 ψ hψ.continuous 0)
        (nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F) := by
  let P : ℝ → AngularL2 := cylinderTestL2 ψ hψ.continuous
  let AP : ℝ → AngularL2 := fun t => negativeLaplacianAngularL2
    (fun θ => ψ (t, θ)) (smooth_cylinder_sphere_slice hψ t)
  have hA (i : AngularIndex) (t : ℝ) :
      inner ℝ (angularBasis i) (AP t) = angularEigenvalue i * inner ℝ (angularBasis i) (P t) := by
    dsimp only [P, AP]
    rw [cylinderTestL2_eq_smoothAngularL2 hψ]
    exact angularBasis_negativeLaplacian_coefficient _ _ i
  have h := nativeHalfHighDirichlet_full_hilbert_green hκ0 hκ1 V hV hV0 F
    (contDiff_cylinderTestL2 hψ) (hasCompactSupport_cylinderTestL2 hψ.continuous hc)
    (continuous_negativeLaplacian_test_curve hψ) hA
  rw [second_deriv_cylinderTestL2 hψ] at h
  have hAPIntegral (t : ℝ) :
      inner ℝ (AP t) (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t) =
        ∫ θ : S, (-sphereD.laplacian (fun x => ψ (t, x)) θ) *
          (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ) θ ∂angularVolume := by
    dsimp only [AP]
    rw [L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [negativeLaplacianAngularL2_ae (fun x => ψ (t, x))
      (smooth_cylinder_sphere_slice hψ t)] with θ hθ
    rw [hθ]
    simp [mul_comm]
  dsimp only [AP] at hAPIntegral
  simp only [real_inner_smul_right, halfEnd_inner_cylinderTestL2_eq_integral,
    hAPIntegral] at h
  simpa only [cylinderTimeDerivative, P, AP, halfEnd_inner_cylinderTestL2_eq_integral] using h

#print axioms nativeHalfHighDirichlet_full_hilbert_green
#print axioms nativeHalfHighDirichlet_original_joint_green

end Yamabe3.Analysis.Delaunay

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit6

-- Original proof unit: Yamabe3.Analysis.Cylinder.NativeForcedHalfEndFullGreen
section NativeHalfEndGreenProofUnit7

/-!
# Original half-end Green formula with genuine physical-volume tests

All joint representatives below are those of the original constructed
Hilbert solution and source.  The time region, volume Jacobian, native
spherical Laplacian, coefficient eight, and entrance functional are
retained through the same calculation.

The metric in this module is the actual Euclidean metric of the model
ball.  No identification with a different original-manifold source or
with a completed H1 conormal is made by changing notation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Manifold ContDiff Bundle Topology RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The genuine restricted cylinder product measure corresponding to
the punctured unit ball under logarithmic polar coordinates. -/
def nativeHalfEndCylinderVolume : Measure (ℝ × S) :=
  (volume.restrict (Ioi (0 : ℝ))).prod angularVolume

theorem integrable_nativeHalfEndCylinderVolume {f : ℝ × S → ℝ}
    (hf : Integrable f (volume.prod angularVolume)) :
    Integrable f nativeHalfEndCylinderVolume := by
  rw [nativeHalfEndCylinderVolume,
    show (volume.restrict (Ioi (0 : ℝ))).prod angularVolume =
      (volume.prod angularVolume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set S)) by
        rw [← Measure.prod_restrict, Measure.restrict_univ]]
  exact hf.integrableOn

/-- A compact actual joint test pairs with the given representative by
the original Hilbert curve's iterated native spherical integral. -/
theorem native_halfEnd_joint_pair_integral
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {η : ℝ × S → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun p => w p * η p) nativeHalfEndCylinderVolume ∧
      (∫ p, w p * η p ∂nativeHalfEndCylinderVolume) =
        ∫ t in Ioi (0 : ℝ), ∫ θ : S, η (t, θ) * (U t : S → ℝ) θ ∂angularVolume := by
  have hi := integrable_nativeHalfEndCylinderVolume
    (native_joint_compact_pair_integrable hU hw hae hη hc)
  refine ⟨hi, ?_⟩
  rw [nativeHalfEndCylinderVolume] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    filter_upwards [hae t] with θ hθ
    rw [hθ, mul_comm]

/-- The true cylinder test operator for the exact bounded continuous
potential used by the original forced half-end. -/
def nativeHalfEndCylinderTest (V : ℝ →ᵇ ℝ) (ψ : ℝ × S → ℝ) (p : ℝ × S) : ℝ :=
  cylinderTimeDerivative (cylinderTimeDerivative ψ) p - (1 / 4) * ψ p +
    V p.1 * ψ p - (-sphereD.laplacian (fun θ => ψ (p.1, θ)) p.2)

theorem continuous_nativeHalfEndCylinderTest (V : ℝ →ᵇ ℝ) {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ) :
    Continuous (nativeHalfEndCylinderTest V ψ) :=
  (((smooth_cylinderTimeDerivative (smooth_cylinderTimeDerivative hψ)).continuous.sub
    (continuous_const.mul hψ.continuous)).add
    ((V.continuous.comp continuous_fst).mul hψ.continuous)).sub
    (continuous_native_sphere_laplacian_family hψ).neg

theorem hasCompactSupport_nativeHalfEndCylinderTest (V : ℝ →ᵇ ℝ) {ψ : ℝ × S → ℝ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (nativeHalfEndCylinderTest V ψ) :=
  (((hasCompactSupport_cylinderTimeDerivative
    (hasCompactSupport_cylinderTimeDerivative hc)).sub hc.mul_left).add hc.mul_left).sub
    (hasCompactSupport_sphere_laplacian_family hc).neg

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The original joint representatives satisfy all compact smooth joint
tests on positive time, including nonzero entrance tests.  Integrability
is proved, and the boundary term is the original entrance derivative. -/
theorem native_forced_halfEnd_original_joint_product_green
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun p => w p * nativeHalfEndCylinderTest V ψ p) nativeHalfEndCylinderVolume ∧
      Integrable (fun p => (Real.exp (-2 * p.1) * z p) * ψ p) nativeHalfEndCylinderVolume ∧
      (∫ p, w p * nativeHalfEndCylinderTest V ψ p ∂nativeHalfEndCylinderVolume) =
        (∫ p, (Real.exp (-2 * p.1) * z p) * ψ p ∂nativeHalfEndCylinderVolume) +
        inner ℝ (cylinderTestL2 ψ hψ.continuous 0)
          (nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F) := by
  have hU := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hF : Continuous (fun t : ℝ => nativeHighProjection (F t.toNNReal)) :=
    nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)
  have hD := native_halfEnd_joint_pair_integral hU hw hwAE
    (smooth_cylinderTimeDerivative (smooth_cylinderTimeDerivative hψ)).continuous
    (hasCompactSupport_cylinderTimeDerivative (hasCompactSupport_cylinderTimeDerivative hc))
  have hZ := native_halfEnd_joint_pair_integral hU hw hwAE hψ.continuous hc
  have hP := native_halfEnd_joint_pair_integral hU hw hwAE
    ((V.continuous.comp continuous_fst).mul hψ.continuous) hc.mul_left
  have hA := native_halfEnd_joint_pair_integral hU hw hwAE
    (continuous_native_sphere_laplacian_family hψ).neg
    (hasCompactSupport_sphere_laplacian_family hc).neg
  have hS := native_halfEnd_joint_pair_integral hF hz hzAE
    ((by fun_prop : Continuous (fun p : ℝ × S => Real.exp (-2 * p.1))).mul hψ.continuous)
    hc.mul_left
  simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply] at hP hA hS
  have hSrcEq : (fun p : ℝ × S => z p * (Real.exp (-2 * p.1) * ψ p)) =
      (fun p : ℝ × S => (Real.exp (-2 * p.1) * z p) * ψ p) := by
    funext p
    ring
  have hSrc : Integrable (fun p => (Real.exp (-2 * p.1) * z p) * ψ p)
      nativeHalfEndCylinderVolume := hSrcEq ▸ hS.1
  have hJ := native_halfEnd_joint_pair_integral hU hw hwAE
    (continuous_nativeHalfEndCylinderTest V hψ) (hasCompactSupport_nativeHalfEndCylinderTest V hc)
  have hJIntegral : (∫ p, w p * nativeHalfEndCylinderTest V ψ p ∂nativeHalfEndCylinderVolume) =
      (∫ p, w p * cylinderTimeDerivative (cylinderTimeDerivative ψ) p ∂nativeHalfEndCylinderVolume) -
      (1 / 4) * (∫ p, w p * ψ p ∂nativeHalfEndCylinderVolume) +
      (∫ p, w p * (V p.1 * ψ p) ∂nativeHalfEndCylinderVolume) -
      (∫ p, w p * (-sphereD.laplacian (fun θ => ψ (p.1, θ)) p.2) ∂nativeHalfEndCylinderVolume) := by
    have heq : (fun p => w p * nativeHalfEndCylinderTest V ψ p) =
        (fun p => (w p * cylinderTimeDerivative (cylinderTimeDerivative ψ) p -
          (1 / 4) * (w p * ψ p) + w p * (V p.1 * ψ p)) -
          w p * (-sphereD.laplacian (fun θ => ψ (p.1, θ)) p.2)) := by
      funext p
      dsimp only [nativeHalfEndCylinderTest]
      ring
    have hSplit0 := integral_sub ((hD.1.sub (hZ.1.const_mul (1 / 4))).add hP.1) hA.1
    have hSplit1 := integral_add (hD.1.sub (hZ.1.const_mul (1 / 4))) hP.1
    have hSplit2 := integral_sub hD.1 (hZ.1.const_mul (1 / 4))
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply] at hSplit0 hSplit1 hSplit2
    rw [heq, hSplit0, hSplit1, hSplit2, integral_const_mul]
  refine ⟨hJ.1, hSrc, ?_⟩
  rw [hJIntegral, hD.2, hZ.2, hP.2, hA.2, ← hSrcEq, hS.2]
  have h := nativeHalfHighDirichlet_original_joint_green hκ0 hκ1 V hV hV0 F hψ hc
  simpa only [cylinderTimeDerivative, mul_assoc, integral_const_mul] using h

/-- The physical test operator is actually differentiated.  This
identity is for the same model metric and the same singular potential. -/
theorem native_halfEnd_joint_test_operator (V : ℝ →ᵇ ℝ) {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ)
    {r : ℝ} (hr : 0 < r) (θ : S) :
    -8 * euclideanD.laplacian (cylinderLift ψ) (r • (θ : E)) -
      8 * nativeHalfEndPotentialCoefficient V (r • (θ : E)) * cylinderLift ψ (r • (θ : E)) =
      (-8 * radialScale r / r ^ 2) * nativeHalfEndCylinderTest V ψ (-Real.log r, θ) := by
  have hn : ‖r • (θ : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  rw [laplacian_cylinderLift hψ hr θ, nativeHalfEndPotentialCoefficient, hn,
    cylinderLift_smul _ hr θ]
  dsimp only [nativeHalfEndCylinderTest, cylinderTimeDerivative]
  ring

theorem logCylinderWeight_halfEnd_joint_pairing (V : ℝ →ᵇ ℝ) (w : ℝ × S → ℝ)
    {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ) :
    logCylinderWeight (fun x : E => cylinderLift w x *
      (-8 * euclideanD.laplacian (cylinderLift ψ) x -
        8 * nativeHalfEndPotentialCoefficient V x * cylinderLift ψ x)) =
      fun p => -8 * (w p * nativeHalfEndCylinderTest V ψ p) := by
  funext p
  change Real.exp (-3 * p.1) * (cylinderLift w (Real.exp (-p.1) • (p.2 : E)) *
    (-8 * euclideanD.laplacian (cylinderLift ψ) (Real.exp (-p.1) • (p.2 : E)) -
      8 * nativeHalfEndPotentialCoefficient V (Real.exp (-p.1) • (p.2 : E)) *
        cylinderLift ψ (Real.exp (-p.1) • (p.2 : E)))) = _
  rw [native_halfEnd_joint_test_operator V hψ (Real.exp_pos _) p.2,
    cylinderLift_smul w (Real.exp_pos _) p.2, Real.log_exp, neg_neg]
  rw [← mul_assoc, logarithmic_pairing_factor]
  ring

/-- Full physical-volume transposed Green formula for every genuine
smooth joint cylinder test, with no zero-entrance restriction on the
test.  The given original physical source appears literally. -/
theorem native_forced_halfEnd_original_physical_joint_green
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {ψ : ℝ × S → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) :
    IntegrableOn (fun x : E => cylinderLift w x *
      (-8 * euclideanD.laplacian (cylinderLift ψ) x -
        8 * nativeHalfEndPotentialCoefficient V x * cylinderLift ψ x))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    IntegrableOn (fun x : E => physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x *
      cylinderLift ψ x) (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift w x *
      (-8 * euclideanD.laplacian (cylinderLift ψ) x -
        8 * nativeHalfEndPotentialCoefficient V x * cylinderLift ψ x)) =
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * cylinderLift ψ x) +
      inner ℝ (cylinderTestL2 ψ hψ.continuous 0)
        ((-8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F) := by
  obtain ⟨hJ, hS, hEq⟩ := native_forced_halfEnd_original_joint_product_green
    hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE hψ hc
  have hφ := contDiff_cylinderLift_of_compact hψ hc
  have hQ : Measurable (nativeHalfEndPotentialCoefficient V) :=
    (V.continuous.measurable.comp (Real.measurable_log.comp measurable_norm).neg).div
      (measurable_norm.pow_const 2)
  have hΔ : Measurable (euclideanD.laplacian (cylinderLift ψ)) :=
    (euclideanD.contMDiff_laplacian hφ.contMDiff).continuous.measurable
  have hG : Measurable (fun x : E => cylinderLift w x *
      (-8 * euclideanD.laplacian (cylinderLift ψ) x -
        8 * nativeHalfEndPotentialCoefficient V x * cylinderLift ψ x)) :=
    (measurable_cylinderLift hw).mul ((measurable_const.mul hΔ).sub
      ((measurable_const.mul hQ).mul hφ.continuous.measurable))
  have hGF : Measurable (fun x : E =>
      physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * cylinderLift ψ x) :=
    (measurable_physicalForcing
      ((by fun_prop : Measurable (fun p : ℝ × S => Real.exp (-2 * p.1))).mul hz)).mul
      hφ.continuous.measurable
  have hPJ := native_halfEnd_integral_of_log_pullback hG
    (by
      rw [logCylinderWeight_halfEnd_joint_pairing V w hψ]
      exact hJ.const_mul (-8))
  have hPS := native_halfEnd_integral_of_log_pullback hGF
    (by
      rw [logCylinderWeight_forcing_pairing]
      exact hS.const_mul (-8))
  have hJphysical : (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift w x *
      (-8 * euclideanD.laplacian (cylinderLift ψ) x -
        8 * nativeHalfEndPotentialCoefficient V x * cylinderLift ψ x)) =
      -8 * ∫ p, w p * nativeHalfEndCylinderTest V ψ p ∂nativeHalfEndCylinderVolume := by
    rw [hPJ.2, logCylinderWeight_halfEnd_joint_pairing V w hψ,
      nativeHalfEndCylinderVolume, integral_prod _ hJ]
    simp only [integral_const_mul]
  have hSphysical : (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * cylinderLift ψ x) =
      -8 * ∫ p, (Real.exp (-2 * p.1) * z p) * ψ p ∂nativeHalfEndCylinderVolume := by
    rw [hPS.2, logCylinderWeight_forcing_pairing, nativeHalfEndCylinderVolume,
      integral_prod _ hS]
    simp only [integral_const_mul]
  refine ⟨hPJ.1, hPS.1, ?_⟩
  rw [hJphysical, hSphysical, hEq, real_inner_smul_right]
  ring

/-- The value of a genuine continuous cylinder test on the actual unit
sphere is its zero-time slice.  Only this test is restricted to the
sphere; the solution's volume representative is never restricted. -/
theorem native_halfEnd_smooth_test_boundary_pairing
    (ψ : ℝ × S → ℝ) (hψ : Continuous ψ) (N : AngularL2) :
    inner ℝ (cylinderTestL2 ψ hψ 0) N =
      ∫ θ : S, cylinderLift ψ (θ : E) * (N : S → ℝ) θ ∂angularVolume := by
  calc
    _ = ∫ θ : S, ψ (0, θ) * (N : S → ℝ) θ ∂angularVolume := by
      simp only [L2.inner_def, setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [cylinderTestL2_ae ψ hψ 0] with θ hθ
      rw [hθ]
      simp [mul_comm]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun θ => by
        have hlift : cylinderLift ψ (θ : E) = ψ (0, θ) := by
          simpa only [one_smul, radialScale, Real.log_one, neg_zero, zero_div,
            Real.exp_zero, one_mul] using cylinderLift_smul ψ (r := 1) (by norm_num) θ
        dsimp only
        rw [hlift]

/-- Genuine physical transposed Green formula for every smooth compact
Euclidean test avoiding the missing point.  The test may cross the unit
sphere and have any boundary value.  Its boundary term is an actual
native sphere-volume pairing with the original entrance derivative.

This is the model-ball formula for the original physical source.  It is
not a formula for a different manifold metric or for a renamed source. -/
theorem native_forced_halfEnd_original_physical_green
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hzero : (0 : E) ∉ tsupport φ) :
    IntegrableOn (fun x : E => cylinderLift w x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    IntegrableOn (fun x : E => physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * φ x)
      (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift w x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) =
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * φ x) +
      ∫ θ : S, φ (θ : E) *
        (((-8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F : AngularL2)
          : S → ℝ) θ ∂angularVolume := by
  obtain ⟨ψ, hψ, hψc, he⟩ := exists_compact_smooth_cylinder_test hφ hc hzero
  have h := native_forced_halfEnd_original_physical_joint_green
    hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE hψ hψc
  rw [native_halfEnd_smooth_test_boundary_pairing ψ hψ.continuous,
    he] at h
  exact h

/-- The proved physical Green formula is independent of the chosen
volume representatives of the same physical solution and source.
No almost-everywhere relation is restricted to the boundary. -/
theorem native_forced_halfEnd_original_physical_green_ae
    (F : ℝ≥0 →ᵇ AngularL2) {w z : ℝ × S → ℝ}
    (hw : Measurable w) (hz : Measurable z)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ))
    {u f : E → ℝ}
    (hu : u =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})] cylinderLift w)
    (hf : f =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})]
      physicalForcing (fun p => Real.exp (-2 * p.1) * z p))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hzero : (0 : E) ∉ tsupport φ) :
    IntegrableOn (fun x : E => u x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    IntegrableOn (fun x : E => f x * φ x) (Metric.ball (0 : E) 1 \ {(0 : E)}) ∧
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, u x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) =
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, f x * φ x) +
      ∫ θ : S, φ (θ : E) *
        (((-8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F : AngularL2)
          : S → ℝ) θ ∂angularVolume := by
  obtain ⟨hIu, hIf, hEq⟩ := native_forced_halfEnd_original_physical_green
    hκ0 hκ1 V hV hV0 F hw hz hwAE hzAE hφ hc hzero
  have hUp : (fun x : E => u x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x))
      =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})]
      (fun x : E => cylinderLift w x *
      (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) :=
    hu.mono fun x hx => by dsimp only; rw [hx]
  have hFp : (fun x : E => f x * φ x)
      =ᵐ[volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})]
      (fun x : E => physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x * φ x) :=
    hf.mono fun x hx => by dsimp only; rw [hx]
  refine ⟨hIu.congr hUp.symm, hIf.congr hFp.symm, ?_⟩
  rw [integral_congr_ae hUp, integral_congr_ae hFp]
  exact hEq

#print axioms native_halfEnd_joint_pair_integral
#print axioms native_forced_halfEnd_original_joint_product_green
#print axioms native_halfEnd_joint_test_operator
#print axioms native_forced_halfEnd_original_physical_joint_green
#print axioms native_halfEnd_smooth_test_boundary_pairing
#print axioms native_forced_halfEnd_original_physical_green
#print axioms native_forced_halfEnd_original_physical_green_ae

end Yamabe3.Analysis.SpherePolar

end -- original anonymous noncomputable section
end NativeHalfEndGreenProofUnit7

-- Additional axiom checks for the actual joint test producers.
#print axioms Yamabe3.Analysis.Delaunay.smooth_cylinderTimeDerivative
#print axioms Yamabe3.Analysis.Delaunay.contDiff_cylinderTestL2
#print axioms Yamabe3.Analysis.Delaunay.hasDerivAt_cylinderTestL2
#print axioms Yamabe3.Analysis.Delaunay.second_deriv_cylinderTestL2
#print axioms Yamabe3.Analysis.Delaunay.hasCompactSupport_cylinderTestL2
#print axioms Yamabe3.Analysis.Delaunay.continuous_native_sphere_laplacian_family
#print axioms Yamabe3.Analysis.Delaunay.continuous_negativeLaplacian_test_curve
