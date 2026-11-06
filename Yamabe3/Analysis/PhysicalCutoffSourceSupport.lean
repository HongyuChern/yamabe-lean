import Yamabe3.Analysis.WeakCutoffCriticalGlobal
import Yamabe3.Analysis.NativeChartCriticalTransport
import Yamabe3.Analysis.UniformElliptic.HalfEndAnnularComparison

/-! Actual physical support of the zero-extended residual, including
its source-free inner ball and untruncated chart identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem physicalCutoffAnnulus_norm_bounds (s a:ℝ) (ha:0<a) {x:E}
    (hx:x∈physicalCutoffAnnulus halfEndBasicAnnulus s a) :
    a*Real.exp (-s)/2<‖x‖ ∧ ‖x‖<2*(a*Real.exp (-s)) := by
  change (1/2:ℝ)<‖Real.exp (s-Real.log a) • x‖ ∧ ‖Real.exp (s-Real.log a) • x‖<2 at hx
  have hid:Real.exp (s-Real.log a)*(a*Real.exp (-s))=1:=by
    rw [mul_comm a,←mul_assoc,←Real.exp_add,show s-Real.log a+(-s)= -Real.log a by ring,
      Real.exp_neg,Real.exp_log ha]
    exact inv_mul_cancel₀ ha.ne'
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hx
  constructor
  · nlinarith only [hx.1,hid,Real.exp_pos (s-Real.log a)]
  · nlinarith only [hx.2,hid,Real.exp_pos (s-Real.log a)]

theorem physicalCutoffSource_zero_inner (χ u:E→ℝ) (s a:ℝ) (ha:0<a) {x:E}
    (hx:x∈Metric.ball (0:E) (a*Real.exp (-s)/2)) :
    physicalCutoffSource halfEndBasicAnnulus χ u s a x=0 := by
  apply physicalCutoffSource_zero_off_annulus
  intro hh
  have h:‖x‖<a*Real.exp (-s)/2:=by simpa using hx
  exact (not_lt_of_ge (physicalCutoffAnnulus_norm_bounds s a ha hh).1.le) h

theorem physicalCutoffSource_compact_indicator_eq (χ u:E→ℝ) (s a:ℝ) (ha:0<a)
    {K:Set E} (hK:Metric.closedBall (0:E) (2*(a*Real.exp (-s)))⊆K) :
    K.indicator (physicalCutoffSource halfEndBasicAnnulus χ u s a)=
      physicalCutoffSource halfEndBasicAnnulus χ u s a := by
  funext x
  by_cases hx:x∈K
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    symm
    apply physicalCutoffSource_zero_off_annulus
    intro hh
    exact hx (hK (by simpa using (physicalCutoffAnnulus_norm_bounds s a ha hh).2.le))

theorem native_physicalCutoffSource_zero_inner (e:OpenPartialHomeomorph E M)
    (χ u:E→ℝ) (s a:ℝ) (ha:0<a) (K:Set E)
    (hs:Metric.ball (0:E) (a*Real.exp (-s)/2)⊆e.source) :
    ∀y∈e '' Metric.ball (0:E) (a*Real.exp (-s)/2),
      nativeCompactChartFunction e K (physicalCutoffSource halfEndBasicAnnulus χ u s a) y=0 := by
  rintro y ⟨x,hx,rfl⟩
  rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hs hx)]
  by_cases h:x∈K
  · rw [indicator_of_mem h,physicalCutoffSource_zero_inner χ u s a ha hx]
  · exact indicator_of_notMem h _

#print axioms physicalCutoffAnnulus_norm_bounds
#print axioms physicalCutoffSource_zero_inner
#print axioms physicalCutoffSource_compact_indicator_eq
#print axioms native_physicalCutoffSource_zero_inner
end Yamabe3.Analysis.SpherePolar
