import Yamabe3.Analysis.NativeBCFPhysicalRowPairing
import Yamabe3.Analysis.NativeWeakJacobianLocality

/-! The genuine finite full BCF rows reconstruct ONE weak differential
operator on the physical window. Weak derivatives in different open
shell neighborhoods are identified by restriction uniqueness. No shell
boundary term or pointwise choice of weak derivative is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeFinite_full_BCF_global_weak_operator
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ) {u:E→ℝ} (hu:MemWkp 2 2 u univ)
    (N:ℕ) (J:Fin N→nativeCollarJetClosure)
    (hJ:∀i:Fin N,(J i).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weightedPhysicalDilation (nativeOuterLogShellCenter i) u)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    (∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V)+
        nativeBCFCollarErrorCLM g (a*Real.exp (-nativeOuterLogShellCenter i))
          (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V)) (J i).val)) (nativePhysicalPairTestL2 φ hφ hc h0))=
      ∫x in nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0),
        (nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
          g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x:=by
  let H:E→ℝ:=fun x=>nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
    g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x
  let W:Fin N→Set E:=fun i=>nativeScaledSourceShell (nativeOuterLogShellCenter i)
  have hφm:MemLp φ 2 (volume:Measure E):=hφ.continuous.memLp_of_hasCompactSupport hc
  have hlocal(i:Fin N):H=ᵐ[volume.restrict (W i)]
      (fun x=>nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow (nativeOuterLogShellCenter i)) g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x):=by
    have hr:=nativeWeakRescaledDelaunayJacobian_mono (nativePhysicalScaleWindow_open (nativeOuterLogShellCenter i))
      (subset_univ _) hu g a (fun _=>0) 0
    have hs:W i⊆nativePhysicalScaleWindow (nativeOuterLogShellCenter i):=preimage_mono nativeSourceShell_subset_collar
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) hr] with x hx
    exact congrArg (fun r:ℝ=>r-g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x) hx
  have hm(i:Fin N):MemLp H 2 (volume.restrict (W i)):=by
    have hl:=nativeBCF_shell_actual_weak_source_memLp g a (nativeOuterLogShellCenter i) V (J i) (hJ i)
    exact ((memLp_indicator_iff_restrict (nativeScaledSourceShell_measurable _)).mp hl).ae_eq (hlocal i).symm
  have hi(i:Fin N):IntegrableOn (fun x=>H x*φ x) (W i):=(hm i).integrable_mul (hφm.restrict _)
  have hUnion:IntegrableOn (fun x=>H x*φ x) (⋃i:Fin N,W i):=integrableOn_finite_iUnion.mpr hi
  have hp(i:Fin N):inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V)+
        nativeBCFCollarErrorCLM g (a*Real.exp (-nativeOuterLogShellCenter i))
          (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) V)) (J i).val)) (nativePhysicalPairTestL2 φ hφ hc h0)=
        ∫x in W i,H x*φ x:=by
    have hh:=nativeBCF_same_field_shell_pairing g a (nativeOuterLogShellCenter i) V (J i) (hJ i) φ hφ hc h0
    apply hh.trans
    apply integral_congr_ae
    filter_upwards [hlocal i] with x hx
    exact congrArg (fun r:ℝ=>r*φ x) hx.symm
  have hsum:=hasSum_integral_iUnion (fun i:Fin N=>nativeScaledSourceShell_measurable (nativeOuterLogShellCenter i))
    (nativeScaledOuterShell_disjoint N) hUnion
  have he:(∑i:Fin N,∫x in W i,H x*φ x)=∫x in nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0),H x*φ x:=by
    simpa only [tsum_fintype,W,nativeScaledOuterWindow_union] using hsum.tsum_eq
  exact (Finset.sum_congr rfl (fun i _=>hp i)).trans he

#print axioms nativeFinite_full_BCF_global_weak_operator
end Yamabe3.Analysis.SpherePolar
