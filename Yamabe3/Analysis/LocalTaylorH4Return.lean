import Yamabe3.Analysis.TaylorRemainderH4Graph
import Yamabe3.Analysis.NativeRegularH4PrincipalError

/-! Bounded linear return of one locally smooth family to its TRUE four
low jets plus the SAME weighted H4 remainder. Compact extensions are
proof devices only; their exterior choices do not enter the output. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def localFamilyLowJetLinear (P:X →ₗ[ℝ] (E3→ℝ))
    (hP:∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5)) : X →ₗ[ℝ] RegularLowJet where
  toFun W := (P W 0,fderiv ℝ (P W) 0)
  map_add' W Z := by
    apply Prod.ext
    · exact congrFun (map_add P W Z) 0
    · change fderiv ℝ (P (W+Z)) 0=fderiv ℝ (P W) 0+fderiv ℝ (P Z) 0
      rw [map_add,fderiv_add]
      · exact ((hP W).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))).differentiableAt (by simp)
      · exact ((hP Z).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))).differentiableAt (by simp)
  map_smul' c W := by
    apply Prod.ext
    · exact congrFun (map_smul P c W) 0
    · change fderiv ℝ (P (c • W)) 0=c • fderiv ℝ (P W) 0
      rw [map_smul,fderiv_const_smul]
      exact ((hP W).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))).differentiableAt (by simp)

def localFamilyTaylorLinear (P:X →ₗ[ℝ] (E3→ℝ))
    (hP:∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5)) : X →ₗ[ℝ] (E3→ℝ) where
  toFun W := firstTaylorRemainder (P W)
  map_add' W Z := by
    have hh:=map_add (localFamilyLowJetLinear P hP) W Z
    have h0:=congrArg Prod.fst hh
    have hd:=congrArg Prod.snd hh
    funext x
    change P (W+Z) x-P (W+Z) 0-fderiv ℝ (P (W+Z)) 0 x=_
    change P (W+Z) 0=P W 0+P Z 0 at h0
    change fderiv ℝ (P (W+Z)) 0=fderiv ℝ (P W) 0+fderiv ℝ (P Z) 0 at hd
    rw [h0,hd]
    simp only [map_add,Pi.add_apply,ContinuousLinearMap.add_apply,firstTaylorRemainder]
    ring
  map_smul' c W := by
    have hh:=map_smul (localFamilyLowJetLinear P hP) c W
    have h0:=congrArg Prod.fst hh
    have hd:=congrArg Prod.snd hh
    funext x
    change P (c • W) x-P (c • W) 0-fderiv ℝ (P (c • W)) 0 x=_
    change P (c • W) 0=c*P W 0 at h0
    change fderiv ℝ (P (c • W)) 0=c • fderiv ℝ (P W) 0 at hd
    rw [h0,hd]
    simp only [map_smul,Pi.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,RingHom.id_apply,firstTaylorRemainder]
    ring

def localTaylorH4ReturnCost (C B:ℝ) : ℝ :=
  max C (zeroFirstJetH4GraphCost C (firstTaylorRemainderProfileCost C B))

theorem localTaylorH4ReturnCost_nonneg {C B:ℝ} (hC:0≤C) :
    0≤localTaylorH4ReturnCost C B := hC.trans (le_max_left _ _)

theorem exists_localTaylorH4Return (P:X →ₗ[ℝ] (E3→ℝ))
    (hP:∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5))
    (C B:ℝ) (hC:0≤C) (hB:0≤B)
    (hjets:∀W,∀n≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ n (P W) x‖≤C*‖W‖)
    (hprofile:∀W,derivativeProfile 2 (ball (0:E3) 4) 4 (P W)≤ENNReal.ofReal (B*‖W‖)) :
    ∃T:X →L[ℝ] RegularLowH4Space,
      ‖T‖≤localTaylorH4ReturnCost C B ∧
      (∀W,(T W).1=(P W 0,fderiv ℝ (P W) 0)) ∧
      ∀W,EqOn (regularLowH4Field (T W)) (P W) (closedBall (0:E3) 4) := by
  have hex W:∃v:HalfEndPhysicalH4Graph,
      (∀x:HalfEndEntranceBall,halfEndPhysicalH4GraphValue v x=firstTaylorRemainder (P W) x) ∧
      ‖v‖≤zeroFirstJetH4GraphCost C (firstTaylorRemainderProfileCost C B)*‖W‖ := by
    obtain ⟨f,hf,_,hfe⟩:=exists_smooth_compact_extension_near_compact isOpen_ball
      (isCompact_closedBall (0:E3) 4) (closedBall_subset_ball (by norm_num)) (hP W)
    have hp:derivativeProfile 2 (ball (0:E3) 4) 4 f≤ENNReal.ofReal (B*‖W‖) := by
      rw [derivativeProfile_eq_of_local_germs measurableSet_ball
        (fun x hx => hfe x (ball_subset_closedBall hx)) 2 4]
      exact hprofile W
    have hs:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤C*‖W‖ := by
      intro x hx
      rw [(hfe x hx).iteratedFDeriv ℝ 2 |>.self_of_nhds]
      exact hjets W 2 (by norm_num) x hx
    obtain ⟨v,hv,hvb⟩:=exists_firstTaylorRemainderH4Graph hf (by positivity:0≤C*‖W‖)
      (by positivity:0≤B*‖W‖) hs hp
    refine ⟨v,?_,hvb.trans_eq ?_⟩
    · intro x
      rw [hv]
      unfold firstTaylorRemainder
      rw [(hfe x x.2).self_of_nhds,(hfe 0 (mem_closedBall_self (by norm_num))).self_of_nhds,
        (hfe 0 (mem_closedBall_self (by norm_num))).fderiv_eq]
    · unfold zeroFirstJetH4GraphCost firstTaylorRemainderProfileCost
      rw [max_mul_of_nonneg _ _ (norm_nonneg W)]
      congr 1 <;> ring
  let S (W:X):HalfEndPhysicalH4Graph := Classical.choose (hex W)
  have hS W:=Classical.choose_spec (hex W)
  let L:X →ₗ[ℝ] HalfEndPhysicalH4Graph :=
    {toFun:=S
     map_add':=by
      intro W Z
      apply halfEndPhysicalH4GraphValue_injective
      ext x
      change halfEndPhysicalH4GraphValue (S (W+Z)) x=
        halfEndPhysicalH4GraphValue (S W) x+halfEndPhysicalH4GraphValue (S Z) x
      rw [(hS (W+Z)).1,(hS W).1,(hS Z).1]
      exact congrFun (map_add (localFamilyTaylorLinear P hP) W Z) x
     map_smul':=by
      intro c W
      apply halfEndPhysicalH4GraphValue_injective
      ext x
      change halfEndPhysicalH4GraphValue (S (c • W)) x=c*halfEndPhysicalH4GraphValue (S W) x
      rw [(hS (c • W)).1,(hS W).1]
      exact congrFun (map_smul (localFamilyTaylorLinear P hP) c W) x}
  let Q: X →ₗ[ℝ] RegularLowH4Space := (localFamilyLowJetLinear P hP).prod L
  have hQ W:‖Q W‖≤localTaylorH4ReturnCost C B*‖W‖ := by
    change max ‖(P W 0,fderiv ℝ (P W) 0)‖ ‖S W‖≤_
    rw [localTaylorH4ReturnCost,max_mul_of_nonneg _ _ (norm_nonneg W)]
    apply max_le_max
    · apply max_le
      · simpa only [norm_iteratedFDeriv_zero] using hjets W 0 (by norm_num) 0 (mem_closedBall_self (by norm_num))
      · simpa only [norm_iteratedFDeriv_one] using hjets W 1 (by norm_num) 0 (mem_closedBall_self (by norm_num))
    · exact (hS W).2
  let T:=Q.mkContinuous (localTaylorH4ReturnCost C B) hQ
  refine ⟨T,LinearMap.mkContinuous_norm_le _ (localTaylorH4ReturnCost_nonneg hC) hQ,fun W => rfl,?_⟩
  intro W x hx
  change P W 0+fderiv ℝ (P W) 0 x+halfEndEntranceExtension (halfEndPhysicalH4GraphValue (S W)) x=P W x
  rw [halfEndEntranceExtension_of_mem _ hx,(hS W).1]
  unfold firstTaylorRemainder
  ring

#print axioms localTaylorH4ReturnCost_nonneg
#print axioms exists_localTaylorH4Return
end Yamabe3.Analysis.UniformElliptic
