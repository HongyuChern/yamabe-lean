import Yamabe3.Analysis.NativeWeakJacobianLocality

/-! The weak flat model is localized independently of the native metric
operator. Overlapping H2 windows have the same weak derivatives, so the
shell representative is the actual local operator on every open H2 domain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeWeakFlatJacobian (O : Set E) (v : ℝ→ℝ) (phase : ℝ) (u : E→ℝ) : E→ℝ :=
  fun x => weakNegativeLaplacian O u x+annularDelaunayPotential v phase x*u x

def nativePhysicalWeakFlatJacobian (v : ℝ→ℝ) (phase : ℝ) (u : E→ℝ) (x : E) : ℝ :=
  ∑'n,(nativePhysicalShell n).indicator
    (nativeWeakFlatJacobian (nativePhysicalScaleWindow (nativeLogShellCenter n)) v phase u) x

theorem nativePhysicalWeakFlatJacobian_on (v : ℝ→ℝ) (phase : ℝ) (u : E→ℝ)
    (n : ℕ) {x : E} (hx : x∈nativePhysicalShell n) :
    nativePhysicalWeakFlatJacobian v phase u x=
      nativeWeakFlatJacobian (nativePhysicalScaleWindow (nativeLogShellCenter n)) v phase u x := by
  rw [nativePhysicalWeakFlatJacobian,tsum_eq_single n]
  · exact indicator_of_mem hx _
  · intro m hm
    exact indicator_of_notMem (fun hy => (disjoint_left.mp (nativePhysicalShell_disjoint hm)) hy hx) _

theorem nativeWeakFlatJacobian_mono {O D : Set E} (hD : IsOpen D) (hDO : D⊆O)
    {u : E→ℝ} (hu : MemWkp 2 2 u O) (v : ℝ→ℝ) (phase : ℝ) :
    nativeWeakFlatJacobian O v phase u=ᵐ[volume.restrict D] nativeWeakFlatJacobian D v phase u := by
  have hp : (1:ℝ≥0∞)≤2 := by norm_num
  have h1 (j : Fin 3) := chosenWeakPartial'_mono_set_ae hp hD hDO hu.memW1p j
  have h2 (i j : Fin 3) := (chosenWeakPartial'_mono_set_ae hp hD hDO (hu.chosenWeakPartial_mem j).memW1p i).trans
    (chosenWeakPartial'_ae_congr hp hD (h1 j) i)
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (h2 i))] with x h2
  simp only [nativeWeakFlatJacobian,weakNegativeLaplacian,iterWeakPartial,h2]

theorem nativePhysicalWeakFlatJacobian_local {D : Set E} (hD : IsOpen D) {u : E→ℝ}
    (hu : MemWkp 2 2 u D) (hwin : ∀n : ℕ,MemWkp 2 2 u (nativePhysicalScaleWindow (nativeLogShellCenter n)))
    (v : ℝ→ℝ) (phase : ℝ) :
    nativePhysicalWeakFlatJacobian v phase u=ᵐ[volume.restrict (D∩(Metric.ball 0 1 \ {(0:E)}))]
      nativeWeakFlatJacobian D v phase u := by
  have hcover : D∩(Metric.ball 0 1 \ {(0:E)})=⋃n : ℕ,D∩nativePhysicalShell n := by
    rw [←nativePhysicalShell_union,inter_iUnion]
  rw [hcover,ae_eq_restrict_iUnion_iff]
  intro n
  let W := nativePhysicalScaleWindow (nativeLogShellCenter n)
  have hDW : IsOpen (D∩W) := hD.inter (nativePhysicalScaleWindow_open _)
  have hleft := nativeWeakFlatJacobian_mono hDW inter_subset_left hu v phase
  have hright := nativeWeakFlatJacobian_mono hDW inter_subset_right (hwin n) v phase
  have hs : D∩nativePhysicalShell n⊆D∩W := inter_subset_inter_right D (nativePhysicalShell_subset_window n)
  have hlocal := ae_mono (Measure.restrict_mono hs le_rfl) (hright.trans hleft.symm)
  filter_upwards [hlocal,ae_restrict_mem (hD.measurableSet.inter (nativePhysicalShell_measurable n))] with x hx hxs
  rw [nativePhysicalWeakFlatJacobian_on v phase u n hxs.2]
  exact hx

#print axioms nativePhysicalWeakFlatJacobian_on
#print axioms nativeWeakFlatJacobian_mono
#print axioms nativePhysicalWeakFlatJacobian_local
end Yamabe3.Analysis.SpherePolar
