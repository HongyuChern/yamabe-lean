import Yamabe3.Analysis.NativeHomogeneousEntranceEvaluation
import Yamabe3.Analysis.UniformElliptic.BoundedWeakSobolevGraphLift
import Yamabe3.Analysis.UniformElliptic.LocalProfileWeakNormComparison

/-! The actual homogeneous native field has a bounded H4 graph lift.
The field coordinate is retained, and all graph jets are its own weak jets.
This does not assert invariance under a nonzero geometric source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal BigOperators
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def entranceGraphH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] entranceGraphH1Normed

def nativeHomogeneousEntranceValue (g : RiemannianMetric 3 M) (B : M → ℝ)
    (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) {Ω : Set M} (hΩ : IsOpen Ω)
    (e : OpenPartialHomeomorph E M) (a : ℝ) :
    nativeHomogeneousEnergySpace g B hBs Ω →ₗ[ℝ] (Unit → E → ℝ) where
  toFun W _ := (closedBall (0:E) 2).indicator
    (fun x => nativeHomogeneousEnergyRepresentativeLinear g B hBs hΩ W (e (a • x)))
  map_add' W Z := by
    funext i x
    by_cases hx : x ∈ closedBall (0:E) 2
    · simp only [indicator_of_mem hx,map_add,Pi.add_apply]
    · simp only [indicator_of_notMem hx,Pi.add_apply,zero_add]
  map_smul' c W := by
    funext i x
    by_cases hx : x ∈ closedBall (0:E) 2
    · simp only [indicator_of_mem hx,map_smul,Pi.smul_apply,RingHom.id_apply]
    · simp only [indicator_of_notMem hx,Pi.smul_apply,smul_zero,RingHom.id_apply]

private theorem scaled_ball_three_mem {a c : ℝ} (ha : 0<a) (hc : Real.log 32≤c)
    {x : E} (hx : x∈ball (0:E) 3) : a • x∈ball (0:E) (a*Real.exp c/2) := by
  have hec : 32≤Real.exp c :=
    (Real.exp_log (by norm_num : (0:ℝ)<32)).symm.trans_le (Real.exp_le_exp.mpr hc)
  rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
  have hxn : ‖x‖<3 := by simpa only [mem_ball_zero_iff] using hx
  have hmul := mul_le_mul_of_nonneg_left hec ha.le
  nlinarith [mul_lt_mul_of_pos_left hxn ha]

theorem exists_nativeHomogeneous_entrance_graph_lift
    (g : RiemannianMetric 3 M) (hY : 0<Target.yamabeConstant g) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀ : ℝ} (hR₀ : 0<R₀) (hsource : closedBall (0:E) R₀⊆e.source)
    (hcoeff : ∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0=innerSL ℝ) (hρ : gE.pullbackVolumeDensity id 0=1) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ,0≤C ∧ ∀c a : ℝ,
      Real.log 32≤c → 0<a → a*Real.exp c/2≤R₀ → a*Real.exp c/8<δ →
      ∀(B : M→ℝ) (hBs : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B),
      let Ω := e '' ball (0:E) (a*Real.exp c/2)
      ∀hΩ : IsOpen Ω, (∀x∈Ω,B x=0) →
      let P := nativeHomogeneousEntranceValue g B hBs hΩ e a
      CompleteSpace (weakSobolevGraph (ball (0:E) 1) isOpen_ball 4 P) ∧
      ∃L : nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ]
          weakSobolevGraph (ball (0:E) 1) isOpen_ball 4 P,
        (∀W,weakSobolevGraphValue _ _ _ P (L W)=W) ∧
        ‖L‖ ≤ max 1 (C*Real.exp (-Real.log a/2)) := by
  obtain ⟨δ₁,hδ₁,D,hD,hd⟩ := exists_nativeHomogeneousEnergy_entrance_bound g hY gE e he hei hR₀ hsource hcoeff hB hρ
  obtain ⟨δ₂,hδ₂,K,hK,hk⟩ := exists_nativeHomogeneous_entrance_evaluation g hY gE e he hei hR₀ hsource hcoeff hB hρ
  let N : ℝ≥0∞ := ∑ j∈Finset.range (4+1), (Fintype.card (Fin j→Fin 3):ℝ≥0∞)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,(N*D).toReal,ENNReal.toReal_nonneg,?_⟩
  intro c a hc ha hfit hscale B hBs
  dsimp only
  intro hΩ hzero
  let Ω := e '' ball (0:E) (a*Real.exp c/2)
  let P := nativeHomogeneousEntranceValue g B hBs hΩ e a
  let C := (N*D).toReal*Real.exp (-Real.log a/2)
  have hC : 0≤C := mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hy {x : E} (hx : x∈ball (0:E) 3) : e (a • x)∈Ω :=
    mem_image_of_mem e (scaled_ball_three_mem ha hc hx)
  have hPval (W : nativeHomogeneousEnergySpace g B hBs Ω) {x : E}
      (hx : x∈closedBall (0:E) 2) :
      P W () x=nativeHomogeneousEnergyRepresentative g B hBs hΩ W (e (a • x)) := by
    have hx3 : x∈ball (0:E) 3 := (closedBall_subset_ball (by norm_num)) hx
    simp only [P,nativeHomogeneousEntranceValue,LinearMap.coe_mk,AddHom.coe_mk,indicator_of_mem hx,
      nativeHomogeneousEnergyRepresentativeLinear]
    exact indicator_of_mem (hy hx3) _
  have hpc : ∀i : Unit,∀x : E,Continuous (fun W => P W i x) := by
    intro i x
    cases i
    by_cases hx : x∈closedBall (0:E) 2
    · obtain ⟨L,hL,_⟩ := hk c a hc ha hfit (hscale.trans_le (min_le_right _ _)) B hBs hΩ hzero x hx
      exact L.continuous.congr (fun W => (hL W).trans (hPval W hx).symm)
    · have heq : (fun W => P W () x)=fun _ => (0:ℝ) := by
        funext W
        dsimp only [P,nativeHomogeneousEntranceValue,LinearMap.coe_mk,AddHom.coe_mk]
        exact indicator_of_notMem hx _
      rw [heq]
      exact continuous_const
  have hreg (W : nativeHomogeneousEnergySpace g B hBs Ω) :
      MemWkp 4 2 (P W ()) (ball (0:E) 1) ∧
      (iteratedWeakSobolevNorm 4 2 (P W ()) (ball (0:E) 1)).toReal≤C*‖W‖ := by
    let U := nativeHomogeneousEnergyRepresentative g B hBs hΩ W
    have hU := nativeHomogeneousEnergyRepresentative_spec g B hBs hΩ W
    have hs : ball (0:E) (a*Real.exp c/2)⊆e.source :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall hfit).trans hsource)
    have hchart : ContDiffOn ℝ ∞ (U ∘ e) (ball (0:E) (a*Real.exp c/2)) :=
      contDiffOn_native_chart_representative e he hs (fun x hx =>
        hU.1.contMDiffAt (hΩ.mem_nhds (mem_image_of_mem e hx)))
    have hus : ContDiffOn ℝ ∞ (fun x => U (e (a • x))) (ball (0:E) 3) :=
      hchart.comp (contDiff_id.const_smul a).contDiffOn (fun x hx => scaled_ball_three_mem ha hc hx)
    have hv : closure (ball (0:E) 1)⊆ball (0:E) 3 :=
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num))
    have hae : P W ()=ᵐ[volume.restrict (ball (0:E) 1)] (fun x => U (e (a • x))) := by
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
      exact hPval W ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hx)
    have hmem := memWk2_of_local_smooth isOpen_ball (isBounded_ball.isCompact_closure) isOpen_ball hv hus 4
    refine ⟨(MemWkp_congr_ae (by norm_num) isOpen_ball hae).mpr hmem,?_⟩
    rw [wkpNorm_congr_ae (k:=4) (by norm_num) isOpen_ball hae]
    have hh := (actual_weak_norm_le_local_profile isOpen_ball (isBounded_ball.isCompact_closure)
      isOpen_ball hv hus 4).trans (mul_le_mul le_rfl (hd c a hc ha hfit
        (hscale.trans_le (min_le_left _ _)) B hBs hΩ hzero W).2 zero_le zero_le)
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [N])
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)) hh
    convert ht using 1 <;> dsimp only [C] <;>
      simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
        ENNReal.toReal_ofReal (norm_nonneg W)] <;> ring
  refine ⟨weakSobolevGraph_completeSpace _ _ _ P hpc,?_⟩
  let L := boundedWeakSobolevGraphLift (ball (0:E) 1) isOpen_ball 4 P C hC
    (fun W i => by cases i;exact (hreg W).1) (fun W i => by cases i;exact (hreg W).2)
  exact ⟨L,fun W => rfl,boundedWeakSobolevGraphLift_norm_le _ _ _ P C hC _ _⟩

#print axioms nativeHomogeneousEntranceValue
#print axioms exists_nativeHomogeneous_entrance_graph_lift
end Yamabe3.Analysis.SpherePolar
