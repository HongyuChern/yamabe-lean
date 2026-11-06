import Yamabe3.Analysis.NativeScaledPhysicalSourceL2
import Yamabe3.Analysis.NativeWeightedFieldPotentialL2
import Yamabe3.Analysis.NativeWeakPhysicalConformalScaling
import Yamabe3.Analysis.NativeFullZeroSourceH2

/-! The effective A0 source of the SAME singular-potential field.
The original source and the potential-times-field stay separate; no
bounded multiplication on arbitrary H1 functions is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
local notation "Ounit" => (ball (0:E) 1\{(0:E)})

def nativeZeroUnitPotentialProduct (V:ℝ→ᵇℝ) (u:E→ℝ):E→ℝ:=
  (Ounit).indicator (fun x=>nativeHalfEndPotentialCoefficient V x*u x)

def nativeScaledEffectiveSource (gE:RiemannianMetric 3 E) (a:ℝ)
    (f:HalfEndSourceValue) (V:ℝ→ᵇℝ) (u:E→ℝ) (x:E):ℝ:=
  nativeScaledPhysicalSource gE a f x+
    8*(a⁻¹)^2*nativeZeroUnitPotentialProduct V u (a⁻¹ • x)

theorem nativeScaledEffectiveSource_measurable
    (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue)
    (V:ℝ→ᵇℝ) {u:E→ℝ} (hu:Measurable u):
    Measurable (nativeScaledEffectiveSource gE a f V u):=by
  have hm:Measurable (nativeZeroUnitPotentialProduct V u):=
    ((nativeCollarPotential_measurable V).mul hu).indicator
      (isOpen_ball.sdiff isClosed_singleton).measurableSet
  exact (nativeScaledPhysicalSource_measurable gE ha f).add
    ((hm.comp (continuous_id.const_smul a⁻¹).measurable).const_mul _)

theorem nativeScaledEffectiveSource_memLp
    (gE:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (f:HalfEndSourceValue)
    (V:ℝ→ᵇℝ) {u:E→ℝ}
    (hu:MemLp (fun x=>nativeHalfEndPotentialCoefficient V x*u x) 2 (volume.restrict Ounit))
    {K:Set E} (hK:IsCompact K):
    MemLp (nativeScaledEffectiveSource gE a f V u) 2 (volume.restrict K):=by
  have hm:MemLp (nativeZeroUnitPotentialProduct V u) 2 volume:=
    (memLp_indicator_iff_restrict (isOpen_ball.sdiff isClosed_singleton).measurableSet).mpr hu
  have hd:MemLp (fun x:E=>nativeZeroUnitPotentialProduct V u (a⁻¹ • x)) 2 volume:=by
    have hh:=memLp_comp_dilation (r:=a⁻¹) (inv_ne_zero ha.ne')
      (O:=(univ:Set E)) (by simpa only [Measure.restrict_univ] using hm)
    simpa only [preimage_univ,Measure.restrict_univ] using hh
  exact (nativeScaledPhysicalSource_memLp gE ha f hK).add ((hd.restrict K).const_mul _)

theorem nativePhasePotential_physical_dilation
    {κ:ℝ} (p:DelaunayPhaseData κ) {a:ℝ} (ha:0<a) {x:E} (hx:x≠0):
    annularDelaunayPotential p.orbit (p.phase+Real.log a) x=
      -(a⁻¹)^2*nativeHalfEndPotentialCoefficient p.potential (a⁻¹ • x):=by
  rw [fullModelPotential_eq_neg_annular]
  change annularDelaunayPotential p.orbit (p.phase+Real.log a) x=
    -(a⁻¹)^2*(-annularDelaunayPotential p.orbit p.phase (a⁻¹ • x))
  simp only [annularDelaunayPotential,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,
    Real.log_mul (inv_ne_zero ha.ne') (norm_ne_zero_iff.mpr hx),Real.log_inv]
  rw [show p.phase-(-Real.log a+Real.log ‖x‖)=p.phase+Real.log a-Real.log ‖x‖ by ring]
  field_simp [ha.ne',norm_ne_zero_iff.mpr hx]
  <;>ring

theorem nativeScaledEffectiveSource_density_identity
    (gE:RiemannianMetric 3 E) {κ:ℝ} (p:DelaunayPhaseData κ)
    {a:ℝ} (ha:0<a) (f:HalfEndSourceValue) (u:E→ℝ)
    {x:E} (hx:x∈ball (0:E) a\{0}):
    gE.pullbackVolumeDensity id x*nativeScaledEffectiveSource gE a f p.potential u x=
      (a⁻¹)^2*halfEndEuclideanPhysicalSource f (a⁻¹ • x)-
        8*gE.pullbackVolumeDensity id x*annularDelaunayPotential p.orbit
          (p.phase+Real.log a) x*u (a⁻¹ • x):=by
  have hρ:0<gE.pullbackVolumeDensity id x:=
    (gE.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id (by simpa using Function.injective_id)).2
  have hy:a⁻¹ • x∈Ounit:=by
    constructor
    · rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
      have hn:=mem_ball_zero_iff.mp hx.1
      exact (inv_mul_lt_one₀ ha).mpr hn
    · exact smul_ne_zero (inv_ne_zero ha.ne') hx.2
  unfold nativeScaledEffectiveSource nativeZeroUnitPotentialProduct
  rw [nativeScaledPhysicalSource_of_mem gE ha f hx,indicator_of_mem hy,
    nativePhasePotential_physical_dilation p ha hx.2]
  field_simp [ha.ne',hρ.ne']
  <;>ring

#print axioms nativeScaledEffectiveSource_measurable
#print axioms nativeScaledEffectiveSource_memLp
#print axioms nativePhasePotential_physical_dilation
#print axioms nativeScaledEffectiveSource_density_identity
end Yamabe3.Analysis.SpherePolar
