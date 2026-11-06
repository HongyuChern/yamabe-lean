import Yamabe3.Analysis.NativeCutoffPlateauOperator
import Yamabe3.Analysis.NativeOuterCutoffGeometricSender
import Yamabe3.Analysis.NativeOuterWindowReconstruction

/-! The ACTUAL ordered near/far parameters place every near shell in
the genuine outer-cutoff plateau. This is a germ assertion, so all
operator product derivatives are retained correctly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

 theorem nativeNearOuterCutoff_shell_plateau
    {χ:E→ℝ} (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    {m:ℕ} {b S:ℝ} (hb:b≤-(m:ℝ)/2-1) (hS:S≤b-1) (i:Fin m):
    ∀x∈nativeSourceShell,nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ=ᶠ[𝓝 x](fun _=>1):=by
  intro x hx
  have hni:(i.val:ℝ)+1 ≤ (m:ℝ):=by exact_mod_cast i.isLt
  have hn:‖x‖≤Real.exp (1/2:ℝ):=((nativePolarTimeWindow_norm (1/2) x).mp (nativeSourceShell_subset_collar hx)).2.le
  have hsi:-nativeOuterLogShellCenter i≤(m:ℝ)/2:=by
    dsimp only [nativeOuterLogShellCenter]
    linarith
  have hfit:Real.exp (S-nativeOuterLogShellCenter i) • x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))):=by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _≤Real.exp (S-nativeOuterLogShellCenter i)*Real.exp (1/2:ℝ):=
        mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
      _=Real.exp (S-nativeOuterLogShellCenter i+1/2):=by rw [Real.exp_add]
      _≤_:=Real.exp_le_exp.mpr (by linarith)
  change (fun y:E=>χ (Real.exp (S-nativeOuterLogShellCenter i) • y))=ᶠ[𝓝 x](fun _=>1)
  exact (h1 _ hfit).comp_tendsto (continuous_const_smul (Real.exp (S-nativeOuterLogShellCenter i))).continuousAt

 theorem nativeNearOuterCutoff_full_operator_return
    (g:RiemannianMetric 3 E) {a:ℝ} (ha:0<a) (V:ℝ→ᵇℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    {m:ℕ} {b S:ℝ} (hb:b≤-(m:ℝ)/2-1) (hS:S≤b-1) (i:Fin m) (J:nativeCollarJetClosure):
    nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g (a*Real.exp (-nativeOuterLogShellCenter i)) V)
        (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
          (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) J).val)=
    nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g (a*Real.exp (-nativeOuterLogShellCenter i)) V) J.val):=by
  exact nativeFullBCF_cutoff_plateau_shell_return g (mul_pos ha (Real.exp_pos _)) V _
    (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ)
    (nativeNearOuterCutoff_shell_plateau h1 hb hS i) (nativeOuterLogShellCenter i) J

#print axioms nativeNearOuterCutoff_shell_plateau
#print axioms nativeNearOuterCutoff_full_operator_return
end Yamabe3.Analysis.SpherePolar
