import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-! Retain the actual support in the existing smooth compact extension
construction. This is the same genuine cutoff proof, with the support
fact preserved for native compact-H2 test transport. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
variable {d:ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

 theorem exists_smooth_compact_supported_extension_near_compact
    {O K:Set E} (hO:IsOpen O) (hK:IsCompact K) (hKO:K⊆O)
    {u:E→ℝ} (hu:ContDiffOn ℝ ∞ u O):
    ∃v:E→ℝ,ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ tsupport v⊆O ∧
      ∀x∈K,v=ᶠ[𝓝 x]u:=by
  obtain ⟨δ,hδ,hδO⟩:=hK.exists_cthickening_subset_open hO hKO
  obtain ⟨η,hη,hηc,_,hηone,hηO⟩:=SmoothEllipticBilinearForm.exists_cutoff (hK.cthickening (r:=δ)) hO hδO
  refine ⟨fun x=>η x*u x,?_,hηc.mul_right,tsupport_mul_subset_left.trans hηO,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx:x∈O
    · exact hη.contDiffAt.mul (hu.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      have hz:=notMem_tsupport_iff_eventuallyEq.mp (fun h=>hx (hηO h))
      filter_upwards [hz] with y hy
      change η y=0 at hy
      rw [hy,zero_mul]
  · intro x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx)] with y hy
    rw [hηone y (thickening_subset_cthickening δ K hy),one_mul]

#print axioms exists_smooth_compact_supported_extension_near_compact
end Yamabe3.Analysis.SpherePolar
