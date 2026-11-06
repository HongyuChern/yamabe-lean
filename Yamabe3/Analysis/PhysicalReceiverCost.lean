import Yamabe3.Analysis.CriticalReceiverDilation

/-! Exact cost cancellation for the sending physical cutoff and the
receiving inner ball. No operator contraction is assumed from this identity. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic

theorem physicalReceiver_sqrt_cost (a:ℝ) (ha:0<a) (s:ℝ) :
    Real.exp (-Real.log (a*Real.exp (-s)/8)/2)*Real.sqrt a=
      Real.sqrt 8*Real.exp (s/2) := by
  have hl:Real.log (a*Real.exp (-s)/8)=Real.log a-s-Real.log 8:=by
    rw [Real.log_div (mul_pos ha (Real.exp_pos _)).ne' (by norm_num),
      Real.log_mul ha.ne' (Real.exp_pos _).ne',Real.log_exp]
    ring
  have hsa:Real.sqrt a=Real.exp (Real.log a/2):=by rw [Real.exp_half,Real.exp_log ha]
  have hs8:Real.sqrt 8=Real.exp (Real.log 8/2):=by rw [Real.exp_half,Real.exp_log (by norm_num:(0:ℝ)<8)]
  rw [hl,hsa,hs8,←Real.exp_add,←Real.exp_add]
  congr 1
  ring

#print axioms physicalReceiver_sqrt_cost
end Yamabe3.Analysis.UniformElliptic
