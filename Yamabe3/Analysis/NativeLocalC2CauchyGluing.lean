import Yamabe3.Analysis.NativeC2CauchyGluing
import PoincareLib.Geometry.Manifold.PartitionOfUnity.CompactSupport

/-! Actual local C2 fields suffice for native weak gluing. Constructed
compact extensions are used only through germs on the test supports and
on the interface; the original fields and sources remain in the result.
No regularity at a puncture disjoint from the test support is requested. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
namespace Yamabe3.Analysis.EuclideanSphereTrace

/-- The extension is constructed, with unchanged germs on the actual
compact set; it is not an additional extension hypothesis. -/
theorem exists_compact_C2_extension_near_compact
    {O K:Set E} (hO:IsOpen O) (hK:IsCompact K) (hKO:K⊆O)
    {f:E→ℝ} (hf:ContDiffOn ℝ 2 f O):
    ∃F:E→ℝ,ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ ∀x∈K,F=ᶠ[𝓝 x]f:=by
  obtain ⟨χ,hχ,hχc,hχO,_,hχone⟩:=
    PoincareMT.exists_contMDiff_cutoff_of_isCompact (n:=3) hK hO hKO
  have hd:ContDiff ℝ 2 χ:=hχ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨fun x=>χ x*f x,?_,hχc.mul_right,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx:x∈O
    · exact hd.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      have hz:=notMem_tsupport_iff_eventuallyEq.mp (fun ht=>hx (hχO ht))
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hχone x hx] with y hy
    simpa only [Pi.one_apply,one_mul] using congrArg (fun a:ℝ=>a*f y) hy

theorem native_local_C2_cauchy_gluing_no_interface_source
    (g:RiemannianMetric 3 E)
    (hGauss:∀x v:E,g.inner x x v=inner ℝ x v)
    {r:ℝ} (hr:0<r) (c:E→ℝ) (hc:Continuous c)
    {Oi Oo:Set E} (hOi:IsOpen Oi) (hOo:IsOpen Oo)
    {f h:E→ℝ} (hf:ContDiffOn ℝ 2 f Oi) (hh:ContDiffOn ℝ 2 h Oo)
    (hsi:sphere (0:E) r⊆Oi) (hso:sphere (0:E) r⊆Oo)
    (hvalue:∀θ:S,f (r • (θ:E))=h (r • (θ:E)))
    (hnormal:∀θ:S,fderiv ℝ f (r • (θ:E)) (θ:E)=fderiv ℝ h (r • (θ:E)) (θ:E))
    (φ:E→ℝ) (hφ:ContDiff ℝ 2 φ) (hφc:HasCompactSupport φ)
    (hti:tsupport φ∩closedBall (0:E) r⊆Oi)
    (hto:tsupport φ∩{x:E|r≤‖x‖}⊆Oo):
    (∫x,(closedBall (0:E) r).piecewise f h x*
      (-8*g.leviCivitaData.laplacian φ x+c x*φ x) ∂g.volumeMeasure)=
      ∫x,(closedBall (0:E) r).piecewise
        (fun y=>-8*g.leviCivitaData.laplacian f y+c y*f y)
        (fun y=>-8*g.leviCivitaData.laplacian h y+c y*h y) x*φ x ∂g.volumeMeasure:=by
  let Ki:=(tsupport φ∩closedBall (0:E) r)∪sphere (0:E) r
  let Ko:=(tsupport φ∩{x:E|r≤‖x‖})∪sphere (0:E) r
  have hKi:IsCompact Ki:=(hφc.inter_right isClosed_closedBall).union (isCompact_sphere _ _)
  have hKo:IsCompact Ko:=(hφc.inter_right (isClosed_le continuous_const continuous_norm)).union
    (isCompact_sphere _ _)
  obtain ⟨F,hF,hFc,hFg⟩:=exists_compact_C2_extension_near_compact hOi hKi (union_subset hti hsi) hf
  obtain ⟨H,hH,hHc,hHg⟩:=exists_compact_C2_extension_near_compact hOo hKo (union_subset hto hso) hh
  have hsr(θ:S):r • (θ:E)∈sphere (0:E) r:=by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    simpa using θ.property
  have hv(θ:S):F (r • (θ:E))=H (r • (θ:E)):=by
    rw [(hFg _ (Or.inr (hsr θ))).self_of_nhds,(hHg _ (Or.inr (hsr θ))).self_of_nhds]
    exact hvalue θ
  have hn(θ:S):fderiv ℝ F (r • (θ:E)) (θ:E)=fderiv ℝ H (r • (θ:E)) (θ:E):=by
    rw [(hFg _ (Or.inr (hsr θ))).fderiv_eq,(hHg _ (Or.inr (hsr θ))).fderiv_eq]
    exact hnormal θ
  have hweak:=native_c2_cauchy_gluing_no_interface_source g hGauss hr c hc hF hH hFc hHc hv hn φ hφ hφc
  have hl:(fun x=>(closedBall (0:E) r).piecewise F H x*
        (-8*g.leviCivitaData.laplacian φ x+c x*φ x))=
      (fun x=>(closedBall (0:E) r).piecewise f h x*
        (-8*g.leviCivitaData.laplacian φ x+c x*φ x)):=by
    funext x
    by_cases hx:x∈tsupport φ
    · by_cases hb:x∈closedBall (0:E) r
      · simp only [piecewise_eq_of_mem _ _ _ hb]
        rw [(hFg x (Or.inl ⟨hx,hb⟩)).self_of_nhds]
      · have ho:r≤‖x‖:=(lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hb)).le
        simp only [piecewise_eq_of_notMem _ _ _ hb]
        rw [(hHg x (Or.inl ⟨hx,ho⟩)).self_of_nhds]
    · have hz:φ x=0:=image_eq_zero_of_notMem_tsupport hx
      have hd:g.leviCivitaData.laplacian φ x=0:=image_eq_zero_of_notMem_tsupport
        (fun ht=>hx (g.leviCivitaData.tsupport_laplacian_subset φ ht))
      rw [hz,hd]; ring
  have hrhs:(fun x=>(closedBall (0:E) r).piecewise
        (fun y=>-8*g.leviCivitaData.laplacian F y+c y*F y)
        (fun y=>-8*g.leviCivitaData.laplacian H y+c y*H y) x*φ x)=
      (fun x=>(closedBall (0:E) r).piecewise
        (fun y=>-8*g.leviCivitaData.laplacian f y+c y*f y)
        (fun y=>-8*g.leviCivitaData.laplacian h y+c y*h y) x*φ x):=by
    funext x
    by_cases hx:x∈tsupport φ
    · by_cases hb:x∈closedBall (0:E) r
      · have he:=hFg x (Or.inl ⟨hx,hb⟩)
        simp only [piecewise_eq_of_mem _ _ _ hb]
        rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq he,he.self_of_nhds]
      · have ho:r≤‖x‖:=(lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hb)).le
        have he:=hHg x (Or.inl ⟨hx,ho⟩)
        simp only [piecewise_eq_of_notMem _ _ _ hb]
        rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq he,he.self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]
  rw [hl,hrhs] at hweak
  exact hweak

#print axioms exists_compact_C2_extension_near_compact
#print axioms native_local_C2_cauchy_gluing_no_interface_source
end Yamabe3.Analysis.EuclideanSphereTrace
