import Yamabe3.Analysis.NativePhysicalWeakAssembly

/-! The shell representative is independent of the local H2 window:
on every open H2 subdomain it is the same native weak differential
operator. Shell boundaries do not supply spurious distributional terms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeWeakRescaledDelaunayJacobian_mono {O D : Set E} (hD : IsOpen D) (hDO : D⊆O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ → ℝ) (phase : ℝ) :
    nativeWeakRescaledDelaunayJacobian O g ε v phase u=ᵐ[volume.restrict D]
      nativeWeakRescaledDelaunayJacobian D g ε v phase u := by
  have hp : (1:ℝ≥0∞)≤2 := by norm_num
  have h1 (j : Fin 3) := chosenWeakPartial'_mono_set_ae hp hD hDO hu.memW1p j
  have h2 (i j : Fin 3) := (chosenWeakPartial'_mono_set_ae hp hD hDO (hu.chosenWeakPartial_mem j).memW1p i).trans
    (chosenWeakPartial'_ae_congr hp hD (h1 j) i)
  filter_upwards [eventually_all.mpr h1,eventually_all.mpr (fun i => eventually_all.mpr (h2 i))] with x h1 h2
  simp only [nativeWeakRescaledDelaunayJacobian,weakNegativeLaplacian,iterWeakPartial,weakSecondOrderPerturbation,h1,h2]

theorem nativePhysicalWeakJacobian_local {D : Set E} (hD : IsOpen D) {u : E → ℝ}
    (hu : MemWkp 2 2 u D) (hwin : ∀n : ℕ,MemWkp 2 2 u (nativePhysicalScaleWindow (nativeLogShellCenter n)))
    (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ → ℝ) (phase : ℝ) :
    nativePhysicalWeakJacobian g ε v phase u=ᵐ[volume.restrict (D∩(Metric.ball 0 1 \ {(0:E)}))]
      nativeWeakRescaledDelaunayJacobian D g ε v phase u := by
  have hcover : D∩(Metric.ball 0 1 \ {(0:E)})=⋃n : ℕ,D∩nativePhysicalShell n := by
    rw [←nativePhysicalShell_union,inter_iUnion]
  rw [hcover,ae_eq_restrict_iUnion_iff]
  intro n
  let W := nativePhysicalScaleWindow (nativeLogShellCenter n)
  have hDW : IsOpen (D∩W) := hD.inter (nativePhysicalScaleWindow_open _)
  have hleft := nativeWeakRescaledDelaunayJacobian_mono hDW inter_subset_left hu g ε v phase
  have hright := nativeWeakRescaledDelaunayJacobian_mono hDW inter_subset_right (hwin n) g ε v phase
  have hs : D∩nativePhysicalShell n⊆D∩W := inter_subset_inter_right D (nativePhysicalShell_subset_window n)
  have hlocal := ae_mono (Measure.restrict_mono hs le_rfl) (hright.trans hleft.symm)
  filter_upwards [hlocal,ae_restrict_mem (hD.measurableSet.inter (nativePhysicalShell_measurable n))] with x hx hxs
  rw [nativePhysicalWeakJacobian_on g ε v phase u n hxs.2]
  exact hx

#print axioms nativeWeakRescaledDelaunayJacobian_mono
#print axioms nativePhysicalWeakJacobian_local
end Yamabe3.Analysis.SpherePolar
