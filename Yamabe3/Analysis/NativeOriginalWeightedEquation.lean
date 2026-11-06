import Yamabe3.Analysis.NativeWeightedEquation
import Yamabe3.Analysis.NativeWeakPhysicalRow
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! The same original-source native weak equation under the actual
weighted dilation. The metric scale and orbit phase are transported
with their exact factors, retaining the literal normalized source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration
local notation "O" => (Metric.ball (0:E) 1 \ {(0:E)})

theorem nativeOriginalSource_weighted_weakJacobian
    (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ→ℝ) (phase : ℝ)
    (f : HalfEndPhysicalH2SourceGraph) {u : E→ℝ} (hu : MemWkpLocally 4 u O)
    (he : ∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆O →
      nativeWeakRescaledDelaunayJacobian U g ε v phase u=ᵐ[volume.restrict U]
        (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8))
    (s : ℝ) {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : ∀x∈closure V,Real.exp (-s) • x∈O) :
    MemWkp 4 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) V ∧
    nativeWeakRescaledDelaunayJacobian V g (ε*Real.exp (-s)) v (phase+s)
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))=ᵐ[volume.restrict V]
        actualWeightedSourceSlice f s := by
  let r := Real.exp (-s)
  have hr : 0<r := Real.exp_pos _
  let h : E ≃ₜ E := Homeomorph.smulOfNeZero r hr.ne'
  let W := h '' V
  have hW : IsOpen W := h.isOpenMap V hV
  have hWc : IsCompact (closure W) := by
    rw [show closure W=h '' closure V from (h.image_closure V).symm]
    exact hVc.image h.continuous
  have hWO : closure W⊆O := by
    rw [show closure W=h '' closure V from (h.image_closure V).symm]
    rintro _ ⟨x,hx,rfl⟩
    exact hVO x hx
  have huW := memWkp_on_precompact_of_locally hu hW hWc hWO
  have heW := he W hW hWc hWO
  have hpre : (fun x : E => r • x) ⁻¹' W=V := by
    change h ⁻¹' (h '' V)=V
    exact h.injective.preimage_image V
  have hup := memWkp_comp_dilation hr.ne' hW (by norm_num) 4 huW
  rw [hpre] at hup
  refine ⟨MemWkp.const_smul (by norm_num : (1:ℝ≥0∞)≤2) hV hup (Real.exp (3*s/2)),?_⟩
  have hd := nativeWeakRescaledDelaunayJacobian_dilation hr hW
    (fun x hx => (hWO (subset_closure hx)).2) (huW.le_of_le (by norm_num : 2≤4)) g ε v phase
  have hsrc := ae_comp_dilation hr.ne' heW
  rw [hpre] at hd hsrc
  have hphase : phase-Real.log r=phase+s := by dsimp only [r];rw [Real.log_exp];ring
  rw [hphase] at hd
  have hc := nativeWeakRescaledDelaunayJacobian_const_mul hV (hup.le_of_le (by norm_num : 2≤4))
    g (ε*r) v (phase+s) (Real.exp (3*s/2))
  filter_upwards [hd,hsrc,hc,ae_restrict_mem hV.measurableSet] with x hd hs hc hx
  have hx0 : x≠0 := by
    intro hzero
    have hh := (hVO x (subset_closure hx)).2
    exact hh (by simp only [hzero,smul_zero,mem_singleton_iff])
  rw [hc,hd,hs]
  exact (mul_assoc _ _ _).symm.trans (weighted_source_physical_identity f s hx0)

#print axioms nativeOriginalSource_weighted_weakJacobian
end Yamabe3.Analysis.UniformElliptic
