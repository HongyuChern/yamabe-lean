import Yamabe3.Analysis.CriticalReceiverDilation
import Yamabe3.Analysis.WeakLaplacianDilation

/-! The true bounded linear critical dilation from Euclidean L6 to
local L2. The actual representative and dimension-three cost exp(-t/2)
are retained; point evaluation of Lp is used only modulo a.e. identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
private instance criticalSix_ge_one:Fact (1 ≤ (6:ℝ≥0∞)) := ⟨by norm_num⟩
local notation "E" => EuclideanSpace ℝ (Fin 3)

private def receiverDilationLinear (O:Set E) (t:ℝ)
    (hm:∀u:Lp ℝ 6 (volume:Measure E),MemLp (fun x:E=>u (Real.exp t • x)) 2 (volume.restrict O)) :
    Lp ℝ 6 (volume:Measure E) →ₗ[ℝ] Lp ℝ 2 (volume.restrict O) where
  toFun u:=(hm u).toLp _
  map_add' u v:=by
    apply Lp.ext
    have h:=ae_comp_dilation (Real.exp_ne_zero t) (ae_restrict_of_ae (s:=univ) (Lp.coeFn_add u v))
    simp only [preimage_univ,Measure.restrict_univ] at h
    filter_upwards [(hm (u+v)).coeFn_toLp,(hm u).coeFn_toLp,(hm v).coeFn_toLp,
      Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _),ae_restrict_of_ae (s:=O) h] with x hs hu hv hx hadd
    rw [hs,hx]
    simp only [Pi.add_apply] at hadd ⊢
    rw [hu,hv,hadd]
  map_smul' c u:=by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have h:=ae_comp_dilation (Real.exp_ne_zero t) (ae_restrict_of_ae (s:=univ) (Lp.coeFn_smul c u))
    simp only [preimage_univ,Measure.restrict_univ] at h
    filter_upwards [(hm (c • u)).coeFn_toLp,(hm u).coeFn_toLp,
      Lp.coeFn_smul c ((hm u).toLp _),ae_restrict_of_ae (s:=O) h] with x hs hu hx hsmul
    rw [hs,hx]
    simp only [Pi.smul_apply] at hsmul ⊢
    rw [hu,hsmul]

theorem exists_criticalReceiver_dilation_CLM (O:Set E) (hvol:volume O < ⊤) :
    ∃C:ℝ,0 ≤ C ∧ ∀t:ℝ,
      ∃T:Lp ℝ 6 (volume:Measure E) →L[ℝ] Lp ℝ 2 (volume.restrict O),
        ‖T‖ ≤ C*Real.exp (-t/2) ∧ ∀u:Lp ℝ 6 (volume:Measure E),
          (T u:E→ℝ)=ᵐ[volume.restrict O]fun x:E=>u (Real.exp t • x) := by
  obtain ⟨D,hD,hd⟩:=exists_criticalReceiver_dilation_L2_bound O hvol
  refine ⟨D.toReal,ENNReal.toReal_nonneg,fun t=>?_⟩
  have hm (u:Lp ℝ 6 (volume:Measure E)):MemLp (fun x:E=>u (Real.exp t • x)) 2 (volume.restrict O) :=
    (hd u (Lp.memLp u) t).1
  let L:=receiverDilationLinear O t hm
  have hb (u:Lp ℝ 6 (volume:Measure E)):‖L u‖ ≤ (D.toReal*Real.exp (-t/2))*‖u‖ := by
    have ht:=ENNReal.toReal_mono (by finiteness) (hd u (Lp.memLp u) t).2
    change ‖(hm u).toLp (fun x:E=>u (Real.exp t • x))‖ ≤ _
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,Lp.norm_def,mul_assoc] using ht
  let T:=L.mkContinuous (D.toReal*Real.exp (-t/2)) hb
  exact ⟨T,LinearMap.mkContinuous_norm_le _ (by positivity) hb,fun u=>(hm u).coeFn_toLp⟩

#print axioms exists_criticalReceiver_dilation_CLM
end Yamabe3.Analysis.UniformElliptic
