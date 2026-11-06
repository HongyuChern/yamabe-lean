import Yamabe3.Analysis.NativeFullBubbleNativePotential
import Yamabe3.Analysis.SmoothCompactSupportedExtension
import Yamabe3.Analysis.Green.NativeChartTestExtension

/-! Actual smooth compact spatial bubble truncation, with the literal
hard-minus-smooth residual retained. The omitted multiplier is dominated
by the actual scaled bubble tail, not called a compensation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.NirenbergEuclidean Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

 theorem exists_nativeSmoothBubble_spatial_cutoff {L:ℝ} (hL:0<L):
    ∃χ:E→ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀x:E,0≤χ x ∧ χ x≤1) ∧
      (∀x∈closedBall (0:E) L,χ x=1) ∧ tsupport χ⊆ball (0:E) (2*L):=by
  obtain ⟨χ,hχ,hχc,hr,hχone,hχs⟩:=SmoothEllipticBilinearForm.exists_cutoff
    (isCompact_closedBall (0:E) L) isOpen_ball (closedBall_subset_ball (by linarith:L<2*L))
  exact ⟨χ,hχ,hχc,fun x=>hr (mem_range_self x),hχone,hχs⟩

variable {M:Type*} [TopologicalSpace M]

 def nativeScaledSmoothBubblePotential (e:OpenPartialHomeomorph E M) (τ a:ℝ) (χ:E→ℝ):M→ℝ:=
  coordinateExtension e (fun x:E=>χ (a⁻¹ • x)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)))

 theorem nativeSmoothBubble_compact_chart_identity
    (e:OpenPartialHomeomorph E M) (K:Set E) (τ a:ℝ) (χ:E→ℝ)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆K):
    nativeScaledSmoothBubblePotential e τ a χ=
      nativeCompactChartFunction e K
        (fun x:E=>χ (a⁻¹ • x)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))):=by
  let U:E→ℝ:=fun x=>χ (a⁻¹ • x)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))
  change coordinateExtension e U=coordinateExtension e (K.indicator U)
  apply congrArg (fun f:E→ℝ=>coordinateExtension e f)
  funext x
  change U x=K.indicator U x
  by_cases hx:x∈K
  · exact (indicator_of_mem hx _).symm
  · rw [indicator_of_notMem hx]
    have hz:χ (a⁻¹ • x)=0:=image_eq_zero_of_notMem_tsupport (f:=fun y:E=>χ (a⁻¹ • y)) (fun h=>hx (hs h))
    change χ (a⁻¹ • x)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))=0
    rw [hz,zero_mul]

 theorem nativeSmoothBubble_difference_tail_dominated
    (e:OpenPartialHomeomorph E M) (K:Set E) (τ:ℝ) {a:ℝ} (ha:0<a) (s:ℝ) (χ:E→ℝ)
    (hr:∀x:E,0≤χ x ∧ χ x≤1)
    (hχone:∀x∈closedBall (0:E) (Real.exp s),χ x=1)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆K):
    ∀y:M,‖nativeScaledFullBubblePotential e K τ a y-nativeScaledSmoothBubblePotential e τ a χ y‖≤
      ‖nativeCompactChartFunction e K (fullBubbleScaledTail τ s (Real.log a)) y‖:=by
  rw [nativeSmoothBubble_compact_chart_identity e K τ a χ hs,fullBubbleScaledTail_actual_scale ha]
  intro y
  by_cases hy:y∈e.target
  · simp only [nativeScaledFullBubblePotential,nativeCompactChartFunction,coordinateExtension_apply e _ hy]
    by_cases hx:e.symm y∈K
    · simp only [indicator_of_mem hx]
      by_cases ht:Real.exp s<‖a⁻¹ • e.symm y‖
      · rw [fullBubblePotentialTail,indicator_of_mem (show a⁻¹ • e.symm y∈{x:E|Real.exp s<‖x‖} from ht)]
        have hχ:=hr (a⁻¹ • e.symm y)
        have hsmall:|1-χ (a⁻¹ • e.symm y)|≤1:=by rw [abs_of_nonneg (by linarith)];linarith
        rw [show (a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • e.symm y)-
          χ (a⁻¹ • e.symm y)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • e.symm y))=
          (1-χ (a⁻¹ • e.symm y))*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • e.symm y)) by ring,
          Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_right hsmall (abs_nonneg _)).trans_eq (one_mul _)
      · rw [hχone _ (mem_closedBall_zero_iff.mpr (le_of_not_gt ht)),one_mul,sub_self,norm_zero]
        exact norm_nonneg _
    · simp only [indicator_of_notMem hx,sub_self,norm_zero]
      exact le_rfl
  · simp only [nativeScaledFullBubblePotential,nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,sub_self,norm_zero]
    exact le_rfl

section Smooth
variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
 theorem nativeScaledSmoothBubblePotential_smooth
    (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (τ:ℝ) {a:ℝ} (ha:0<a) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆e.source):
    ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χ):=by
  let U:E→ℝ:=fun x=>χ (a⁻¹ • x)*((a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))
  have hU:ContDiff ℝ ∞ U:=(hχ.comp (contDiff_id.const_smul a⁻¹)).mul
    (contDiff_const.mul ((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).comp (contDiff_id.const_smul a⁻¹)))
  have hUc:HasCompactSupport U:=(hc.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))).mul_right
  exact contMDiff_coordinateExtension e hei hU hUc (tsupport_mul_subset_left.trans hs)
end Smooth

#print axioms exists_nativeSmoothBubble_spatial_cutoff
#print axioms nativeSmoothBubble_compact_chart_identity
#print axioms nativeSmoothBubble_difference_tail_dominated
#print axioms nativeScaledSmoothBubblePotential_smooth
end Yamabe3.Analysis.SpherePolar
