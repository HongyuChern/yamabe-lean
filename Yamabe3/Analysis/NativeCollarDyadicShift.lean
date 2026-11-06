import Yamabe3.Analysis.NativeCollarDyadicPartition

/-! The shifted actual cutoff partition, used strictly inside the unit
interface. It reconstructs the same original function, with no value
condition imposed at the single removed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

theorem nativeCollarDyadicPiece_partial_sum_shift (χ:E→ℝ) (k N:ℕ) (x:E) :
    (∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp (((n+k:ℕ):ℝ)/4) • x))=
      nativeCollarDyadicCutoff χ k x-nativeCollarDyadicCutoff χ (N+k) x := by
  induction N with
  | zero=>simp
  | succ N ih=>
    rw [Finset.sum_range_succ,ih,nativeCollarDyadicPiece_scale]
    rw [show (N+k)+1=(N+1)+k by omega]
    ring

theorem nativeCollarDyadicPiece_tendsto_sum_shift {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) (k:ℕ) {x:E} (hx:x≠0) :
    Tendsto (fun N:ℕ=>∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp (((n+k:ℕ):ℝ)/4) • x))
      atTop (𝓝 (nativeCollarDyadicCutoff χ k x)) := by
  obtain ⟨N₀,hN₀⟩:=eventually_atTop.mp (nativeCollarDyadicCutoff_eventually_zero hs hx)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [nativeCollarDyadicPiece_partial_sum_shift,hN₀ (N+k) (hN.trans (Nat.le_add_right N k)),sub_zero]

#print axioms nativeCollarDyadicPiece_partial_sum_shift
#print axioms nativeCollarDyadicPiece_tendsto_sum_shift
end Yamabe3.Analysis.SpherePolar
