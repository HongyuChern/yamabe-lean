import Yamabe3.Analysis.NativeCollarCutoffCommutator
import Yamabe3.Analysis.NativeShellWeightedPolar
import PoincareLib.Geometry.Manifold.PartitionOfUnity.CompactSupport

/-! A fixed genuine smooth cutoff whose ALL first and second derivative
support lies inside the source shell. It equals one near the origin;
no discontinuous radial characteristic function is used as a cutoff. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.Iteration

private theorem partial_const_germ {χ:E→ℝ} {x:E} {c:ℝ}
    (hχ:χ=ᶠ[𝓝 x](fun _=>c)) (i:Fin 3) :
    partialDeriv i χ=ᶠ[𝓝 x](fun _=>0) := by
  filter_upwards [hχ.fderiv (𝕜:=ℝ)] with y hy
  simp only [partialDeriv,hy,fderiv_const_apply,zero_apply]

theorem exists_nativeShellCutoff :
    ∃χ:E→ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)) ∧
      (∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) ∧
      ∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
        partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0 := by
  have hrad:Real.exp (-(1/8:ℝ)) < Real.exp (1/8:ℝ) := Real.exp_lt_exp.mpr (by norm_num)
  obtain ⟨χ,hχ,hc,hs,_,h1⟩:=PoincareMT.exists_contMDiff_cutoff_of_isCompact (n:=3)
    (isCompact_closedBall (0:E) (Real.exp (-(1/8:ℝ)))) isOpen_ball (closedBall_subset_ball hrad)
  refine ⟨χ,hχ.contDiff,hc,hs,h1,?_⟩
  intro x hx i
  have hg:∃c:ℝ,χ=ᶠ[𝓝 x](fun _=>c) := by
    by_cases hi:x∈closedBall (0:E) (Real.exp (-(1/8:ℝ)))
    · exact ⟨1,h1 x hi⟩
    · have hout:x∉ball (0:E) (Real.exp (1/8:ℝ)) := by
        intro ho
        have hl:Real.exp (-(1/8:ℝ)) < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hi
        have hu:‖x‖ < Real.exp (1/8:ℝ) := mem_ball_zero_iff.mp ho
        have ht: x∈nativePolarTimeWindow (Ioo (-(1/8:ℝ)) (1/8)) :=
          (nativePolarTimeWindow_norm (1/8) x).mpr ⟨hl,hu⟩
        apply hx
        exact ⟨ht.1,by linarith [ht.2.1],by linarith [ht.2.2]⟩
      have ht:x∉tsupport χ := fun h=>hout (hs h)
      refine ⟨0,?_⟩
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds ht] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
  obtain ⟨c,hg⟩:=hg
  have hi:=partial_const_germ hg i
  have hii:=partial_const_germ hi i
  exact ⟨hi.self_of_nhds,hii.self_of_nhds⟩

#print axioms exists_nativeShellCutoff
end Yamabe3.Analysis.SpherePolar
