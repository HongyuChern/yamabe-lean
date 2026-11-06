import Yamabe3.Analysis.NativeMatchedPhysicalEquation
import Yamabe3.Analysis.NativeWeakPhysicalRow

/-! Physical shell rows are the actual weak native operator of one common
H2 function on open physical windows. No independent jet or shellwise
solution is substituted for that function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativePhysicalWeakJacobian (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ → ℝ)
    (phase : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  ∑'n,(nativePhysicalShell n).indicator
    (nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow (nativeLogShellCenter n)) g ε v phase u) x

theorem nativePhysicalWeakJacobian_on (g : RiemannianMetric 3 E) (ε : ℝ) (v : ℝ → ℝ)
    (phase : ℝ) (u : E → ℝ) (n : ℕ) {x : E} (hx : x∈nativePhysicalShell n) :
    nativePhysicalWeakJacobian g ε v phase u x=
      nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow (nativeLogShellCenter n)) g ε v phase u x := by
  rw [nativePhysicalWeakJacobian,tsum_eq_single n]
  · exact indicator_of_mem hx _
  · intro m hm
    exact indicator_of_notMem (fun hy => (disjoint_left.mp (nativePhysicalShell_disjoint hm)) hy hx) _

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
  (g : RiemannianMetric 3 E) (ε : ℝ) (F : NativeSpectralSourceL2)

theorem nativeMatchedPhysicalRow_same_weak_operator {u : E → ℝ} (s : ℝ)
    (he : ((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    (fun x => Real.exp (s/2)*(nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
      (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F) : E → ℝ) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g ε p.orbit p.phase u := by
  let J := nativeMatchedDelaunayJetCLM hκ0 hκ1 B p hp s F
  have hweak := nativeOrbitCollarJacobian_weak_ae g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s) J
  have hcongr := nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g (ε*Real.exp (-s)) p.orbit (p.phase+s) he
  have hc := ae_comp_dilation (Real.exp_ne_zero s) (hweak.trans hcongr)
  have hu := (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) he).mp
    (nativeMatchedDelaunay_memH2 hκ0 hκ1 B p hp s F)
  have hphys := nativeWeakPhysicalRow_identity g ε p.orbit p.phase s hu
  filter_upwards [hc,hphys] with x hc hp
  exact (congrArg (fun z : ℝ => Real.exp (s/2)*z) hc).trans hp

theorem nativeMatchedPhysicalJacobian_same_weak_operator {u : E → ℝ}
    (he : ∀s : ℝ,((nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F).1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    nativeMatchedPhysicalJacobian hκ0 hκ1 B p hp g ε F=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      nativePhysicalWeakJacobian g ε p.orbit p.phase u := by
  rw [←nativePhysicalShell_union,ae_eq_restrict_iUnion_iff]
  intro n
  have h := nativeMatchedPhysicalRow_same_weak_operator hκ0 hκ1 B p hp g ε F (nativeLogShellCenter n) (he _)
  have hh := ae_mono (Measure.restrict_mono (nativePhysicalShell_subset_window n) le_rfl) h
  filter_upwards [hh,ae_restrict_mem (nativePhysicalShell_measurable n)] with x hh hx
  rw [nativePhysicalWeakJacobian_on g ε p.orbit p.phase u n hx]
  change nativePhysicalShellAssembly _ x=_
  rw [nativePhysicalShellAssembly_on _ n hx]
  exact hh

#print axioms nativePhysicalWeakJacobian_on
#print axioms nativeMatchedPhysicalRow_same_weak_operator
#print axioms nativeMatchedPhysicalJacobian_same_weak_operator
end Yamabe3.Analysis.SpherePolar
