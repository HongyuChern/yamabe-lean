import Yamabe3.Analysis.NativeExteriorModelJacobian
import Yamabe3.Analysis.NativeOrbitWeakJacobian
import Yamabe3.Analysis.NativeCollarErrorLinearDecay

/-! The actual exterior native geometric residual for the same bounded
cylinder potential and the same H2 jet. The physical coefficient 8,
density and scalar curvature are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.GreenParametrix Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeBCFPotentialError (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ →ᵇ ℝ) (x : E) : ℝ :=
  r^2*nativePotentialDensity g (r • x)-(g.pullbackVolumeDensity id (r • x)-1)*nativeHalfEndPotentialCoefficient V x

theorem nativeBCFPotentialError_continuousOn (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ →ᵇ ℝ) :
    ContinuousOn (nativeBCFPotentialError g r V) {x : E | x≠0} := by
  intro x hx
  have hn : ContinuousAt (fun y : E => Real.log ‖y‖) x :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hx)).comp continuous_norm.continuousAt
  have hq : ContinuousAt (nativeHalfEndPotentialCoefficient V) x :=
    (V.continuous.continuousAt.comp hn.neg).div (continuous_norm.continuousAt.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  exact ((continuousAt_const.mul ((contDiff_nativePotentialDensity g).continuous.continuousAt.comp
    (continuous_const_smul r).continuousAt)).sub
    ((((native_density_smooth_positive g).1.continuous.continuousAt.comp (continuous_const_smul r).continuousAt).sub
      continuousAt_const).mul hq)).continuousWithinAt

def nativeBCFCollarErrorCLM (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ →ᵇ ℝ) :
    NativeCollarJet →L[ℝ] NativeCollarL2 :=
  -nativeCollarGeometricErrorCLM g r+
    (nativeCollarLocalMulCLM (nativeBCFPotentialError g r V) (nativeBCFPotentialError_continuousOn g r V)).comp nativeCollarJetValueCLM

def nativeExteriorGeometricResidualCLM (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ →ᵇ ℝ) :
    NativeCollarJet →L[ℝ] Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar) :=
  (8:ℝ) • nativeNegativeCollarRestrictionCLM.comp (nativeBCFCollarErrorCLM g r V)

def nativeExteriorNativeJacobianCLM (g : RiemannianMetric 3 E) (r : ℝ) (V : ℝ →ᵇ ℝ) :
    NativeCollarJet →L[ℝ] Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar) :=
  (8:ℝ) • nativeNegativeCollarRestrictionCLM.comp (nativeFlatCollarJetCLM V+nativeBCFCollarErrorCLM g r V)

theorem nativeExteriorNativeJacobian_eq_model_add_residual (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (J : NativeCollarJet) :
    nativeExteriorNativeJacobianCLM g r V J=
      nativeExteriorModelJacobianCLM V J+nativeExteriorGeometricResidualCLM g r V J := by
  rw [nativeExteriorModelJacobianCLM_apply]
  simp only [nativeExteriorNativeJacobianCLM,nativeExteriorGeometricResidualCLM,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,map_add,smul_add]
  congr 1
  simp [nativeFlatCollarJetCLM,nativeCollarJetSecondCLM,nativeCollarJetValueCLM,map_neg,smul_neg,neg_smul]
  exact add_comm _ _

theorem nativeBCFCollarError_weak_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (J : nativeCollarJetClosure) :
    (nativeBCFCollarErrorCLM g r V J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => -weakSecondOrderPerturbation nativePoissonEntranceCollar
        (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0) J.val.1 x+
        nativeBCFPotentialError g r V x*(J.val.1 : E → ℝ) x) := by
  let X := nativeCollarGeometricErrorCLM g r J.val
  let Y := nativeCollarLocalMulCLM (nativeBCFPotentialError g r V) (nativeBCFPotentialError_continuousOn g r V) J.val.1
  have hX := nativeCollarJetPerturbation_weak_ae (nativeScaledPrincipalError g r) (nativeScaledFirstError g r)
    (fun _ => 0) (fun i j => (contDiff_nativeScaledPrincipalError g r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError g r j).continuous) continuous_const J
  change (⇑(-X+Y))=ᵐ[_] _
  filter_upwards [Lp.coeFn_add (-X) Y,Lp.coeFn_neg X,hX,
    nativeCollarLocalMulCLM_ae (nativeBCFPotentialError g r V) (nativeBCFPotentialError_continuousOn g r V) J.val.1]
    with x ha hn hx hy
  change (-X+Y : NativeCollarL2) x=_
  rw [ha]
  change (-X : NativeCollarL2) x+Y x=_
  rw [hn]
  change -X x+Y x=_
  exact congrArg₂ (fun a b : ℝ => -a+b) hx hy

theorem nativeExteriorNativeJacobian_weak_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (V : ℝ →ᵇ ℝ) (J : nativeCollarJetClosure) :
    (nativeExteriorNativeJacobianCLM g r V J.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => 8*weakNegativeLaplacian nativePoissonEntranceCollar J.val.1 x-
        8*weakSecondOrderPerturbation nativePoissonEntranceCollar (nativeScaledPrincipalError g r)
          (nativeScaledFirstError g r) (fun _ => 0) J.val.1 x+
        (8*r^2*nativePotentialDensity g (r • x)-
          8*g.pullbackVolumeDensity id (r • x)*nativeHalfEndPotentialCoefficient V x)*(J.val.1 : E → ℝ) x) := by
  let Z := nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val
  have hμ : volume.restrict nativeNegativeEntranceCollar≤volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono inter_subset_left le_rfl
  filter_upwards [Lp.coeFn_smul (8:ℝ) (nativeNegativeCollarRestrictionCLM Z),nativeNegativeCollarRestrictionCLM_ae Z,
    ae_mono hμ (Lp.coeFn_add (nativeFlatCollarJetCLM V J.val) (nativeBCFCollarErrorCLM g r V J.val)),
    ae_mono hμ (nativeFlatCollarJet_weak_ae V J),ae_mono hμ (nativeBCFCollarError_weak_ae g r V J)]
    with x hs hr ha hf he
  change ((8:ℝ) • nativeNegativeCollarRestrictionCLM Z : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) x=_
  rw [hs]
  change 8*nativeNegativeCollarRestrictionCLM Z x=_
  rw [hr]
  change 8*(nativeFlatCollarJetCLM V J.val+nativeBCFCollarErrorCLM g r V J.val : NativeCollarL2) x=_
  rw [ha]
  change 8*(nativeFlatCollarJetCLM V J.val x+nativeBCFCollarErrorCLM g r V J.val x)=_
  rw [hf,he]
  simp only [nativeBCFPotentialError]
  ring

theorem nativeBubbleHighLow_native_residual (g : RiemannianMetric 3 E) (r t₀ : ℝ)
    (c : AngularIndex → ℝ) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (heq : ∀i∈nativeLowIndexFinset,∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t= -c i*bubbleCompensation i t)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    let V := nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))
    let K := nativeBubbleLowCollarJet t₀ q hq+nativePoissonExteriorCollarJet (fullBubbleHighPotential (-t₀)) b hb
    (nativeExteriorNativeJacobianCLM g r V K.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => nativeBubbleCollarCompensation t₀ c x+(nativeExteriorGeometricResidualCLM g r V K.val : E → ℝ) x) := by
  dsimp only
  rw [nativeExteriorNativeJacobian_eq_model_add_residual]
  filter_upwards [Lp.coeFn_add (nativeExteriorModelJacobianCLM _ _) (nativeExteriorGeometricResidualCLM _ _ _ _),
    nativeBubbleHighLowCollar_same_source t₀ c q hq heq b hb] with x ha he
  rw [ha]
  change nativeExteriorModelJacobianCLM _ _ x+nativeExteriorGeometricResidualCLM _ _ _ _ x=_
  rw [he]

#print axioms nativeBCFPotentialError_continuousOn
#print axioms nativeExteriorNativeJacobian_eq_model_add_residual
#print axioms nativeBCFCollarError_weak_ae
#print axioms nativeExteriorNativeJacobian_weak_ae
#print axioms nativeBubbleHighLow_native_residual
end Yamabe3.Analysis.SpherePolar
