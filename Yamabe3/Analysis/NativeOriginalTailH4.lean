import Yamabe3.Analysis.NativeOriginalWeightedH4
import Yamabe3.Analysis.WeightedCollarToAnnulus

/-! A genuine uniform weighted H4 tail estimate for the same native
original-source solution. Actual all-scale H2 jets provide the L2 bound;
small-annulus regularity and a finite dilation cover supply all H4 slices.
The entrance extension and its parameter-uniform bound are separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "H" => (Metric.ball (0:E) 1 \ {(0:E)})

theorem exists_native_original_tail_H4_bound
    (g : RiemannianMetric 3 E) (hB : g.euclideanCoefficients 0=innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ≥0∞,C≠⊤ ∧ ∀ε : ℝ,0 ≤ ε → ε<δ →
      ∀v : ℝ→ℝ,ContDiff ℝ ∞ v →
      (∀t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀t,deriv (deriv v) t=radialForce (v t)) →
      ∀(phase : ℝ) (f : HalfEndPhysicalH2SourceGraph) (u : E→ℝ),MemWkpLocally 4 u H →
      (∀U : Set E,IsOpen U → IsCompact (closure U) → closure U ⊆ H →
        nativeWeakRescaledDelaunayJacobian U g ε v phase u=ᵐ[volume.restrict U]
          (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)) →
      ∀B : ℝ,0 ≤ B →
      (∀s : ℝ,Real.log 2+1 ≤ s → ∃J : nativeCollarJetClosure,
        ((J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] weightedPhysicalDilation s u) ∧ ‖J‖ ≤ B*‖f‖) →
      ∀s : ℝ,4 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤
          C*(ENNReal.ofReal B+1)*ENNReal.ofReal ‖f‖ := by
  let V := nativePolarTimeWindow (Ioo (-(3/8:ℝ)) (3/8))
  let W := nativePolarTimeWindow (Ioo (-(1/4:ℝ)) (1/4))
  have hVO : closure V ⊆ nativePoissonEntranceCollar := nativePolarTimeWindow_nested (by norm_num : (3/8:ℝ)<1/2)
  obtain ⟨δ,hδ,C₀,hC₀,hsmall⟩ := exists_native_original_weighted_H4_bound g hB hρ
    (nativePolarTimeWindow_open (1/2)) (nativePolarTimeWindow_precompact (1/2))
    (fun x hx => nativePolarTimeWindow_closure_offZero (1/2) hx)
    (fun x hx => (nativeEntranceCollar_closure_subset_basic hx).2.le)
    (nativePolarTimeWindow_open (3/8)) (nativePolarTimeWindow_precompact (3/8)) hVO
    (subset_closure.trans hVO)
    (nativePolarTimeWindow_open (1/4)) (nativePolarTimeWindow_precompact (1/4))
    (nativePolarTimeWindow_nested (by norm_num : (1/4:ℝ)<3/8))
  obtain ⟨D,hD,hcover⟩ := exists_weighted_collar_to_annulus_H4_bound
  refine ⟨δ,hδ,D*C₀,by finiteness,?_⟩
  intro ε hε hεδ v hv hb hODE phase f u hu he B hB0 hj s hs
  have hbnd : ∀t : ℝ,Real.log 2+1 ≤ t → MemWkp 4 2 (weightedPhysicalDilation t u) W ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t u) W ≤ C₀*(ENNReal.ofReal B+1)*ENNReal.ofReal ‖f‖ := by
    intro t ht
    obtain ⟨J,hJ,hJn⟩ := hj t ht
    have hh := hsmall ε hε hεδ v hv hb hODE phase f u hu he t ht J hJ
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ ≤ C₀*(ENNReal.ofReal (B*‖f‖)+ENNReal.ofReal ‖f‖) :=
        mul_le_mul le_rfl (add_le_add (ENNReal.ofReal_le_ofReal hJn) le_rfl) zero_le zero_le
      _ = _ := by rw [ENNReal.ofReal_mul hB0];ring
  have hh := hcover u _ hbnd s hs
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

#print axioms exists_native_original_tail_H4_bound
end Yamabe3.Analysis.UniformElliptic
