import Yamabe3.Analysis.NativePointEnergyCutoff

/-! A genuinely constructed sequence of native smooth cutoffs equal to
one near the point, converging to zero in the actual H1 completion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativePointEnergyCutoffSequence
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {R:ℝ} (hR:0<R) (hRK:closedBall (0:E) R⊆K) :
    ∃κ:ℕ→EnergyTest g.leviCivitaData univ,
      (∀n,(κ n:M→ℝ)=ᶠ[𝓝 (e 0)](fun _=>1)) ∧
      Tendsto (fun n=>(κ n:H1Zero g.leviCivitaData univ)) atTop (𝓝 0) := by
  let β:ContDiffBump (0:E):={rIn:=1,rOut:=2,rIn_pos:=by norm_num,rIn_lt_rOut:=by norm_num}
  let c:=min 1 (R/2)
  have hc:0<c:=lt_min (by norm_num) (by positivity)
  let a:ℕ→ℝ:=fun n=>c*(1/2:ℝ)^n
  have ha(n:ℕ):0<a n:=mul_pos hc (pow_pos (by norm_num) _)
  have hac(n:ℕ):a n≤c:=by
    apply mul_le_of_le_one_right hc.le
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have ha1(n:ℕ):a n≤1:=(hac n).trans (min_le_left _ _)
  have haR(n:ℕ):a n≤R/2:=(hac n).trans (min_le_right _ _)
  have hfit(n:ℕ):euclideanDilatedDomain (a n) (closedBall (0:E) β.rOut)⊆K:=by
    intro x hx
    apply hRK
    rw [mem_closedBall,dist_zero_right]
    change (a n)⁻¹ • x∈closedBall (0:E) (2:ℝ) at hx
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (ha n).le)] at hx
    calc
      ‖x‖=(a n)*((a n)⁻¹*‖x‖):=by rw [←mul_assoc,mul_inv_cancel₀ (ha n).ne',one_mul]
      _ ≤ (a n)*2:=mul_le_mul_of_nonneg_left hx (ha n).le
      _ ≤ R:=by linarith only [haR n]
  let κ:ℕ→EnergyTest g.leviCivitaData univ:=fun n=>
    nativeChartPointCutoffTest g e hei β (ha n) ((hfit n).trans hKs)
  refine ⟨κ,fun n=>nativeChartPointCutoffTest_germ g e hei β (ha n) ((hfit n).trans hKs),?_⟩
  have halim:Tendsto a atTop (𝓝 0):=by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0:ℝ)≤1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)).const_mul c
  have hlim:Tendsto (fun n=>(nativeWeakChartBound g e he hei hK hKs*‖nativePointBumpTest β‖)*Real.sqrt (a n))
      atTop (𝓝 0):=by
    have hh:=(Real.continuous_sqrt.continuousAt.tendsto.comp halim).const_mul
      (nativeWeakChartBound g e he hei hK hKs*‖nativePointBumpTest β‖)
    change Tendsto (fun n=>(nativeWeakChartBound g e he hei hK hKs*‖nativePointBumpTest β‖)*Real.sqrt (a n))
      atTop (𝓝 ((nativeWeakChartBound g e he hei hK hKs*‖nativePointBumpTest β‖)*Real.sqrt 0)) at hh
    simpa only [Real.sqrt_zero,mul_zero] using hh
  have hn:Tendsto (fun n=>‖κ n‖) atTop (𝓝 0):=
    squeeze_zero (fun n=>norm_nonneg (κ n))
      (fun n=>nativeChartPointCutoffTest_norm g e he hei hK hKs β (ha n) (ha1 n) (hfit n)) hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Completion.norm_coe] using hn

#print axioms exists_nativePointEnergyCutoffSequence
end Yamabe3.Analysis.SpherePolar
