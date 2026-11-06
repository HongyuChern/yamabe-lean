import Yamabe3.Analysis.NativeSmallCollarJetError
import Yamabe3.Analysis.NativeSmallCollarPotentialError
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives
import Yamabe3.Analysis.NativeFullErrorIdentityC2

/-! Actual native-minus-flat Delaunay error on the same H2 collar jet.
Both principal and potential signs are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay

def nativeFullCollarJetErrorCLM (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  -nativeCollarGeometricErrorCLM g r+
    (nativeCollarPotentialErrorCLM g r v hv phase).comp nativeCollarJetValueCLM

theorem nativeFullCollarJetError_C2_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (u : nativeC2OffZero) :
    (nativeFullCollarJetErrorCLM g r v hv phase (nativeC2CollarJetLinear u) : E → ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar] nativeDelaunayOperatorError g r v phase u.val := by
  let J := nativeC2CollarJetLinear u
  let X := nativeCollarGeometricErrorCLM g r J
  let Y := nativeCollarPotentialErrorCLM g r v hv phase J.1
  have hval := (nativeC2Collar_memLp u.property).1.coeFn_toLp
  change (⇑(-X+Y))=ᵐ[_] _
  filter_upwards [Lp.coeFn_add (-X) Y,Lp.coeFn_neg X,nativeCollarGeometricError_C2_ae g r u,
    nativeCollarPotentialErrorCLM_ae g r v hv phase J.1,hval] with x hadd hneg hX hY hval
  change (-X+Y : NativeCollarL2) x=_
  rw [hadd]
  change (-X : NativeCollarL2) x+Y x=_
  rw [hneg]
  change -X x+Y x=_
  rw [hX,hY]
  change -nativeScaledGeometricError g r u.val x+
    nativeDelaunayPotentialError g r v phase x*(nativeC2CollarValue u.property : E → ℝ) x=_
  have hvx : (nativeC2CollarValue u.property : E → ℝ) x=u.val x := hval
  exact congrArg (fun y => -nativeScaledGeometricError g r u.val x+nativeDelaunayPotentialError g r v phase x*y) hvx

theorem nativeFullCollarJetError_weak_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (J : nativeCollarJetClosure) :
    (nativeFullCollarJetErrorCLM g r v hv phase J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => -weakSecondOrderPerturbation nativePoissonEntranceCollar
        (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0) J.val.1 x+
        nativeDelaunayPotentialError g r v phase x*(J.val.1 : E → ℝ) x) := by
  let X := nativeCollarGeometricErrorCLM g r J.val
  let Y := nativeCollarPotentialErrorCLM g r v hv phase J.val.1
  change (⇑(-X+Y))=ᵐ[_] _
  have hX := nativeCollarJetPerturbation_weak_ae (nativeScaledPrincipalError g r) (nativeScaledFirstError g r)
    (fun _ => 0) (fun i j => (contDiff_nativeScaledPrincipalError g r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError g r j).continuous) continuous_const J
  filter_upwards [Lp.coeFn_add (-X) Y,Lp.coeFn_neg X,hX,
    nativeCollarPotentialErrorCLM_ae g r v hv phase J.val.1] with x hadd hneg hx hy
  change (-X+Y : NativeCollarL2) x=_
  rw [hadd]
  change (-X : NativeCollarL2) x+Y x=_
  rw [hneg]
  change -X x+Y x=_
  have hxx : X x=weakSecondOrderPerturbation nativePoissonEntranceCollar
      (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0) J.val.1 x := hx
  have hyy : Y x=nativeDelaunayPotentialError g r v phase x*(J.val.1 : E → ℝ) x := hy
  rw [hxx,hyy]

theorem exists_uniform_small_native_full_collar_jet_error
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ ∀ r : ℝ,0≤r → r<δ → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0≤v t ∧ v t≤1 ∧ |deriv v t|≤1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) →
      ∀ (phase : ℝ) (J : NativeCollarJet),
      ‖nativeFullCollarJetErrorCLM (g p) r v hv phase J‖≤τ*‖J‖ := by
  have ht : (0:ℝ)<τ/2 := by positivity
  obtain ⟨d,hd,hg⟩ := exists_uniform_small_native_collar_jet_error Λ g hB hρ ht
  obtain ⟨e,he,hp⟩ := exists_uniform_small_native_collar_potential_error Λ g hρ ht
  refine ⟨min d e,lt_min hd he,fun r hr hrδ p hpΛ v hv hb ho phase J => ?_⟩
  have hG := hg r hr (hrδ.trans_le (min_le_left _ _)) p hpΛ J
  have hP := hp r hr (hrδ.trans_le (min_le_right _ _)) p hpΛ v hv hb ho phase J.1
  change ‖-nativeCollarGeometricErrorCLM (g p) r J+nativeCollarPotentialErrorCLM (g p) r v hv phase J.1‖≤_
  calc
    _ ≤ ‖nativeCollarGeometricErrorCLM (g p) r J‖+‖nativeCollarPotentialErrorCLM (g p) r v hv phase J.1‖ := by
      simpa only [norm_neg] using norm_add_le (-nativeCollarGeometricErrorCLM (g p) r J) (nativeCollarPotentialErrorCLM (g p) r v hv phase J.1)
    _ ≤ (τ/2)*‖J‖+(τ/2)*‖J.1‖ := add_le_add hG hP
    _ ≤ (τ/2)*‖J‖+(τ/2)*‖J‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_fst_le J) ht.le)
    _ = _ := by ring

#print axioms nativeFullCollarJetError_C2_ae
#print axioms nativeFullCollarJetError_weak_ae
#print axioms exists_uniform_small_native_full_collar_jet_error
end Yamabe3.Analysis.SpherePolar
