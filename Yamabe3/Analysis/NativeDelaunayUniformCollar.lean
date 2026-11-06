import Yamabe3.Analysis.DelaunayPhaseData
import Yamabe3.Analysis.NativeDelaunayEntranceH4
import Yamabe3.Analysis.BoundaryPhysicalLocalExtension
import Yamabe3.Analysis.UniformFamilyCollar

/-! One physical H4 collar neighborhood and one bound, before the actual
Delaunay orbit, its phase and the original source. The extension agrees
with the one canonical completion, hence with the original positive field.
This does not yet assert the all-scale weighted graph estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0 : E) 1 \ {(0 : E)}

def delaunayPhaseCompletion {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source) : H1Zero nativeWeakEuclideanD O :=
  nativeHalfEndH2SourceCompletion hκ0 hκ1 p.potential p.kernel_bound
    p.potential_nonneg p.potential_smooth f

theorem exists_uniform_delaunay_physical_local_collar
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (a : E) (ha : ‖a‖ = 1) :
    ∃ (N : Set E) (L : DelaunayPhaseData κ → HalfEndHighH2Source → E → ℝ) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N ⊆ halfEndSourceAnnulus ∧ C ≠ ⊤ ∧
      ∀ p f, MemWkp 4 2 (L p f) N ∧
        iteratedWeakSobolevNorm 4 2 (L p f) N ≤ C*ENNReal.ofReal ‖f.1‖ ∧
        EqOn (L p f) (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) (N ∩ O) := by
  obtain ⟨e,χ,U,A,hae,haU,hU,hUc,hUs,het,he,hei,hflat,hone,hA,hreg⟩ :=
    exists_uniform_delaunay_entrance_chart_H4_bound hκ0 hκ1 a ha
  obtain ⟨N,T,B,haN,hN,hNc,hNt,hB,hb⟩ :=
    exists_chart_physical_local_extension e he hei hflat χ hU hone a hae haU
  let L (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source) :=
    T (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))
  refine ⟨N,L,B*A,haN,hN,hNc,hNt.trans het,by finiteness,?_⟩
  intro p f
  have hf := hreg p.orbit p.smooth (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩)
    p.ode p.phase p.potential (fun _ => rfl) p.kernel_bound p.potential_nonneg p.potential_smooth f
  have hh := hb _ hf.1
  refine ⟨hh.1,hh.2.1.trans ?_,hh.2.2⟩
  simpa only [mul_assoc,Poincare.Analysis.Sobolev.BoundaryTangential.halfSpace] using
    mul_le_mul (a := B) le_rfl hf.2 zero_le zero_le

theorem exists_uniform_delaunay_compact_H4_collar
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ (U : Set E) (L : DelaunayPhaseData κ → HalfEndHighH2Source → E → ℝ) (C : ℝ≥0∞),
      IsOpen U ∧ Metric.sphere (0:E) 1 ⊆ U ∧ C ≠ ⊤ ∧
      ∀ p f, HasCompactSupport (L p f) ∧ MemWkp 4 2 (L p f) univ ∧
        iteratedWeakSobolevNorm 4 2 (L p f) univ ≤ C*ENNReal.ofReal ‖f.1‖ ∧
        EqOn (L p f) (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) (U ∩ O) ∧
        L p f =ᵐ[volume.restrict (U ∩ O)]
          cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f) := by
  let J := DelaunayPhaseData κ × HalfEndHighH2Source
  let u (j : J) (x : E) : ℝ := toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 j.1 j.2) x
  let B (j : J) := ENNReal.ofReal ‖j.2.1‖
  have hl : ∀ a ∈ Metric.sphere (0:E) 1,
      ∃ (N : Set E) (L : J → E → ℝ) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ C ≠ ⊤ ∧ ∀ j,
        MemWkp 4 2 (L j) N ∧ iteratedWeakSobolevNorm 4 2 (L j) N ≤ C*B j ∧
          EqOn (L j) (u j) (N ∩ O) := by
    intro a ha
    have han : ‖a‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using ha
    obtain ⟨N,L,C,haN,hN,hNc,hNs,hC,hh⟩ := exists_uniform_delaunay_physical_local_collar hκ0 hκ1 a han
    exact ⟨N,fun j => L j.1 j.2,C,haN,hN,hC,fun j => hh j.1 j.2⟩
  obtain ⟨U,L,C,hU,hKU,hC,hf⟩ := exists_uniform_family_compact_collar 4 O
    (Metric.sphere (0:E) 1) (isCompact_sphere 0 1) u B hl
  refine ⟨U,fun p f => L (p,f),C,hU,hKU,hC,?_⟩
  intro p f
  have hh := hf (p,f)
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,?_⟩
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  filter_upwards [ae_restrict_mem (hU.inter hO).measurableSet,
    ae_restrict_of_ae (nativeHalfEndH2SourceCompletion_rep hκ0 hκ1 p.potential p.kernel_bound
      p.potential_nonneg p.potential_smooth f)] with x hx hr
  rw [hh.2.2.2 hx]
  exact hr.trans (indicator_of_mem hx.2 _)

#print axioms exists_uniform_delaunay_physical_local_collar
#print axioms exists_uniform_delaunay_compact_H4_collar
end Yamabe3.Analysis.UniformElliptic
