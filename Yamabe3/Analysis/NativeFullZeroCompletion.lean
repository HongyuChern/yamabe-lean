import Yamabe3.Analysis.NativeFullZeroWeakEquation
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndCompletionAssembly

/-! The actual zero-entrance remainder of the full-source model field
is realized once in the Euclidean completion. Its real global L2 equation
extends to all completed tests, using the proved dense smooth core. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem nativeCompletion_variational_of_compact_weak {Ω:Set E} (hΩ:IsOpen Ω)
    {u g:E→ℝ} (hu:MemH01 u Ω) (hg:MemLp g 2 (volume.restrict Ω))
    (du:Fin 3→E→ℝ) (hdu:∀i,MemLp (du i) 2 (volume.restrict Ω))
    (hw:∀i,HasWeakPartialDeriv i (du i) u Ω) (he:WeakEquation Ω du g)
    (z:H1Zero D Ω) (hz:(toL2 D Ω z:E→ℝ) =ᵐ[volume] Ω.indicator u) :
    ∀η:H1Zero D Ω, gradientEnergy D Ω z η=∫x in Ω,g x*(toL2 D Ω η:E→ℝ) x := by
  apply nativeCompletion_variational_extension hΩ hg z
  intro η
  rw [nativeEuclidean_memH01_gradient_pairing hΩ hu du hdu hw z hz]
  have hi (i:Fin 3):Integrable (fun x=>du i x*fderiv ℝ (η:E→ℝ) x (EuclideanSpace.single i 1))
      (volume.restrict Ω):=(hdu i).integrable_mul ((nativeEuclidean_test_derivative_memLp Ω η i).restrict Ω)
  rw [←integral_finsetSum Finset.univ (fun i _=>hi i)]
  refine (he (η:E→ℝ) η.smooth.contDiff η.hasCompactSupport η.support_subset).trans ?_
  have hη:(toL2 D Ω (η:H1Zero D Ω):E→ℝ) =ᵐ[volume] (η:E→ℝ):=by
    have hh:(testToL2 D Ω η:E→ℝ) =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] (η:E→ℝ):=
      η.memLp.coeFn_toLp
    simpa only [toL2_coe,native_euclideanMetric_volumeMeasure] using hh
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hη] with x hx
  rw [hx]

variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)

def fullModelZeroCompletion (f:HalfEndPhysicalH2SourceGraph) : H1Zero D O :=
  (exists_nativeEuclideanH01_of_memH01 (Metric.isOpen_ball.sdiff isClosed_singleton)
    (fullModelZeroEntranceField_H01 hκ0 hκ1 p f)).choose

theorem fullModelZeroCompletion_rep (f:HalfEndPhysicalH2SourceGraph) :
    (toL2 D O (fullModelZeroCompletion hκ0 hκ1 p f):E→ℝ) =ᵐ[volume]
      (O).indicator (fullModelZeroEntranceField hκ0 hκ1 p f) :=
  (exists_nativeEuclideanH01_of_memH01 (Metric.isOpen_ball.sdiff isClosed_singleton)
    (fullModelZeroEntranceField_H01 hκ0 hκ1 p f)).choose_spec

theorem fullModelZeroCompletion_variational (f:HalfEndPhysicalH2SourceGraph) :
    ∀η:H1Zero D O, gradientEnergy D O (fullModelZeroCompletion hκ0 hκ1 p f) η=
      ∫x in O,fullModelZeroNormalizedRHS hκ0 hκ1 p f x*(toL2 D O η:E→ℝ) x := by
  obtain ⟨hu,hg,du,hdu,hw,he⟩:=fullModelZeroEntrance_same_weak_equation hκ0 hκ1 p f
  exact nativeCompletion_variational_of_compact_weak (Metric.isOpen_ball.sdiff isClosed_singleton)
    hu hg du hdu hw he _ (fullModelZeroCompletion_rep hκ0 hκ1 p f)

def fullModelZeroCompletionRHS (f:HalfEndPhysicalH2SourceGraph) :
    Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure :=
  let hg:= (fullModelZeroEntrance_same_weak_equation hκ0 hκ1 p f).2.1
  let hG:MemLp ((O).indicator (fullModelZeroNormalizedRHS hκ0 hκ1 p f)) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure:=by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (memLp_indicator_iff_restrict (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet).mpr hg
  hG.toLp _

theorem fullModelZeroCompletion_source (f:HalfEndPhysicalH2SourceGraph) :
    (fullModelZeroCompletionRHS hκ0 hκ1 p f:E→ℝ) =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
      (O).indicator (fun x=>fullModelZeroPhysicalSource p f x/8+
        nativeHalfEndPotentialCoefficient p.potential x*toL2 D O (fullModelZeroCompletion hκ0 hκ1 p f) x) := by
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  have hz:=fullModelZeroCompletion_rep hκ0 hκ1 p f
  have hG:MemLp ((O).indicator (fullModelZeroNormalizedRHS hκ0 hκ1 p f)) 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure:=by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (memLp_indicator_iff_restrict hO.measurableSet).mpr
        (fullModelZeroEntrance_same_weak_equation hκ0 hκ1 p f).2.1
  have hR:(fullModelZeroCompletionRHS hκ0 hκ1 p f:E→ℝ) =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
      (O).indicator (fullModelZeroNormalizedRHS hκ0 hκ1 p f):=hG.coeFn_toLp
  apply hR.trans
  simp only [native_euclideanMetric_volumeMeasure]
  filter_upwards [hz] with x hx
  by_cases h:x∈O
  · simp only [indicator_of_mem h] at hx ⊢
    rw [hx]
    rfl
  · simp only [indicator_of_notMem h]

theorem fullModelZeroCompletion_retained_equation (f:HalfEndPhysicalH2SourceGraph) (η:H1Zero D O) :
    ⟪fullModelZeroCompletion hκ0 hκ1 p f,η⟫_ℝ - 
      ⟪toL2 D O (fullModelZeroCompletion hκ0 hκ1 p f),toL2 D O η⟫_ℝ = 
      ⟪fullModelZeroCompletionRHS hκ0 hκ1 p f,toL2 D O η⟫_ℝ := by
  change gradientEnergy D O (fullModelZeroCompletion hκ0 hκ1 p f) η=
    nativeCompletionRHS (Metric.isOpen_ball.sdiff isClosed_singleton)
      ((fullModelZeroEntrance_same_weak_equation hκ0 hκ1 p f).2.1) η
  rw [nativeCompletionRHS_eq_integral]
  exact fullModelZeroCompletion_variational hκ0 hκ1 p f η

#print axioms nativeCompletion_variational_of_compact_weak
#print axioms fullModelZeroCompletion_rep
#print axioms fullModelZeroCompletion_variational
#print axioms fullModelZeroCompletion_source
#print axioms fullModelZeroCompletion_retained_equation
end Yamabe3.Analysis.UniformElliptic
