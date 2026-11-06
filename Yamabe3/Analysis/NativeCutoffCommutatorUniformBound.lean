import Yamabe3.Analysis.NativeCollarJetMultiplier
import Yamabe3.Analysis.NativeExteriorGeometricResidualBound
import Yamabe3.Analysis.NativeMatchedJacobianRowBound

/-! The genuine cutoff commutator has a radius-independent bound on
one closed jet space. The scalar-curvature multiplication cancels, so
the operator is exactly the density-divergence commutator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Poincare.Analysis.Elliptic.Iteration
open Yamabe3.Analysis.GreenParametrix
open Poincare.Analysis.Elliptic.InteriorEstimates

def nativeZeroPotentialCollarCLM (g:RiemannianMetric 3 E) (r:ℝ) :
    nativeCollarJetClosure →L[ℝ] NativeCollarL2 :=
  (nativeFlatCollarJetCLM 0+nativeBCFCollarErrorCLM g r 0).comp nativeCollarJetClosure.subtypeL

def nativeCutoffCommutatorCLM (g:RiemannianMetric 3 E) (r:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) : nativeCollarJetClosure →L[ℝ] NativeCollarL2 :=
  (nativeCollarScalarMulCLM χ hχ.continuous).comp (nativeZeroPotentialCollarCLM g r)-
    (nativeZeroPotentialCollarCLM g r).comp (nativeCollarCutoffCLM χ hχ)

theorem nativeZeroPotentialCollarCLM_C2_ae (g:RiemannianMetric 3 E) (r:ℝ) (u:nativeC2OffZero) :
    (nativeZeroPotentialCollarCLM g r (nativeC2CollarJetInclusion u):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x=>principalSource (fun y=>nativeDivergenceMatrix g (r • y)) u.val x+
        r^2*nativePotentialDensity g (r • x)*u.val x := by
  let F:=nativeFlatCollarJetCLM 0 (nativeC2CollarJetLinear u)
  let G:=nativeCollarGeometricErrorCLM g r (nativeC2CollarJetLinear u)
  let T:=nativeCollarLocalMulCLM (nativeBCFPotentialError g r 0)
    (nativeBCFPotentialError_continuousOn g r 0) (nativeC2CollarValue u.property)
  have ht:=nativeCollarLocalMulCLM_ae (nativeBCFPotentialError g r 0)
    (nativeBCFPotentialError_continuousOn g r 0) (nativeC2CollarValue u.property)
  filter_upwards [Lp.coeFn_add F (-G+T),Lp.coeFn_add (-G) T,Lp.coeFn_neg G,
    nativeFlatCollarJet_C2_ae 0 u,nativeCollarGeometricError_C2_ae g r u,ht,
    (nativeC2Collar_memLp u.property).1.coeFn_toLp,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x ha hb hn hf hg ht hu hx
  change (F+(-G+T):NativeCollarL2) x=_
  rw [ha]
  change F x+(-G+T:NativeCollarL2) x=_
  rw [hb]
  change F x+((-G:NativeCollarL2) x+T x)=_
  rw [hn]
  change F x+(-G x+T x)=_
  rw [hf,hg,ht]
  have huv:(nativeC2CollarValue u.property:E→ℝ) x=u.val x := hu
  rw [huv]
  have hux:=u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds
    (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx)))
  rw [nativeScaledGeometricError_eq_negative_principalSource_C2_at g r x hux,
    principalSource_sub_coefficients_C2_at (fun y=>nativeDivergenceMatrix g (r • y)) (fun _=>1)
      (fun i j=>(contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r))
      (fun _ _=>contDiff_const) hux,principalSource_identity_coordinate]
  simp only [nativeBCFPotentialError,nativeHalfEndPotentialCoefficient,
    BoundedContinuousFunction.coe_zero,Pi.zero_apply,zero_div,sub_zero,mul_zero]
  ring

theorem nativeCutoffCommutatorCLM_C2_ae (g:RiemannianMetric 3 E) (r:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (u:nativeC2OffZero) :
    (nativeCutoffCommutatorCLM g r χ hχ (nativeC2CollarJetInclusion u):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      densityCutoffCommutator (fun y=>nativeDivergenceMatrix g (r • y)) χ u.val := by
  have hm:nativeCollarCutoffCLM χ hχ (nativeC2CollarJetInclusion u)=
      nativeC2CollarJetInclusion (nativeC2Cutoff χ hχ u) := by
    apply Subtype.ext
    exact nativeCollarCutoffRawCLM_C2 χ hχ u
  let U:=nativeZeroPotentialCollarCLM g r (nativeC2CollarJetInclusion u)
  let C:=nativeCollarScalarMulCLM χ hχ.continuous U
  let T:=nativeZeroPotentialCollarCLM g r (nativeC2CollarJetInclusion (nativeC2Cutoff χ hχ u))
  have he:nativeCutoffCommutatorCLM g r χ hχ (nativeC2CollarJetInclusion u)=C-T := by
    simp only [nativeCutoffCommutatorCLM,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,hm,C,T,U]
  rw [he]
  filter_upwards [Lp.coeFn_sub C T,nativeCollarScalarMulCLM_ae χ hχ.continuous U,
    nativeZeroPotentialCollarCLM_C2_ae g r u,
    nativeZeroPotentialCollarCLM_C2_ae g r (nativeC2Cutoff χ hχ u),
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hs hc hu ht hx
  change (C-T:NativeCollarL2) x=_
  rw [hs]
  change C x-T x=_
  rw [hc]
  change χ x*U x-T x=_
  rw [hu,ht,densityCutoffCommutator_eq_principal_difference
    (fun y=>nativeDivergenceMatrix g (r • y))
    (fun i j=>(contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r))
    isClosed_singleton.isOpen_compl (hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
    u.property (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))]
  change _=χ x*principalSource (fun y=>nativeDivergenceMatrix g (r • y)) u.val x-
    principalSource (fun y=>nativeDivergenceMatrix g (r • y)) (fun y=>χ y*u.val y) x
  dsimp only [nativeC2Cutoff]
  ring

theorem nativeCutoffCommutatorCLM_eq_density (g:RiemannianMetric 3 E) (r:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    nativeCutoffCommutatorCLM g r χ hχ=
      (densityCutoffCollarCLM (fun y=>nativeDivergenceMatrix g (r • y))
        (fun i j=>(contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)) χ hχ).comp
          nativeCollarJetClosure.subtypeL := by
  apply ContinuousLinearMap.ext
  intro J
  have hc:=isClosed_eq (nativeCutoffCommutatorCLM g r χ hχ).continuous
    ((densityCutoffCollarCLM (fun y=>nativeDivergenceMatrix g (r • y))
      (fun i j=>(contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)) χ hχ).comp
        nativeCollarJetClosure.subtypeL).continuous
  refine nativeC2CollarJetInclusion_dense.induction_on J hc ?_
  intro u
  apply Lp.ext
  exact (nativeCutoffCommutatorCLM_C2_ae g r χ hχ u).trans
    (densityCutoffCollarCLM_C2_ae (fun y=>nativeDivergenceMatrix g (r • y))
      (fun i j=>(contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)) χ hχ u).symm

theorem exists_native_cutoff_commutator_uniform_bound
    {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) :
    ∃ C:ℝ,0 < C ∧ ∀ r:ℝ,0 ≤ r → r ≤ 1 → ∀p∈Λ,
      ‖nativeCutoffCommutatorCLM (g p) r χ hχ‖ ≤ C := by
  obtain ⟨D,hD,hd⟩:=exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ (M:=0) le_rfl
  let B:=3+D
  have hB0:0 < B := by dsimp [B];linarith
  let L:=‖nativeCollarScalarMulCLM χ hχ.continuous‖+‖nativeCollarCutoffCLM χ hχ‖
  have hL:0 ≤ L := by dsimp [L];positivity
  refine ⟨1+L*B,by positivity,fun r hr hr1 p hp=>?_⟩
  have hN (J:nativeCollarJetClosure):‖nativeZeroPotentialCollarCLM (g p) r J‖ ≤ B*‖J‖ := by
    have hf:=nativeFlatCollarJet_norm_bound (0:ℝ→ᵇℝ) J.val
    simp only [norm_zero,zero_mul,add_zero] at hf
    have hg:=hd r hr hr1 p hp 0 (by simp) J.val
    change ‖nativeFlatCollarJetCLM 0 J.val+nativeBCFCollarErrorCLM (g p) r 0 J.val‖ ≤ _
    exact (norm_add_le _ _).trans ((add_le_add hf hg).trans (by
      change 3*‖J.val‖+(D*r)*‖J.val‖ ≤ (3+D)*‖J.val‖
      nlinarith [mul_le_mul_of_nonneg_right hr1 hD.le,norm_nonneg J.val]))
  apply (nativeCutoffCommutatorCLM (g p) r χ hχ).opNorm_le_bound (by positivity)
  intro J
  change ‖nativeCollarScalarMulCLM χ hχ.continuous (nativeZeroPotentialCollarCLM (g p) r J)-
    nativeZeroPotentialCollarCLM (g p) r (nativeCollarCutoffCLM χ hχ J)‖ ≤ _
  calc
    _ ≤ ‖nativeCollarScalarMulCLM χ hχ.continuous (nativeZeroPotentialCollarCLM (g p) r J)‖+
      ‖nativeZeroPotentialCollarCLM (g p) r (nativeCollarCutoffCLM χ hχ J)‖ := norm_sub_le _ _
    _ ≤ ‖nativeCollarScalarMulCLM χ hχ.continuous‖*(B*‖J‖)+
      B*(‖nativeCollarCutoffCLM χ hχ‖*‖J‖) :=
      add_le_add ((nativeCollarScalarMulCLM χ hχ.continuous).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (hN J) (norm_nonneg _)))
        ((hN _).trans (mul_le_mul_of_nonneg_left ((nativeCollarCutoffCLM χ hχ).le_opNorm J) hB0.le))
    _ ≤ _ := by
      change ‖nativeCollarScalarMulCLM χ hχ.continuous‖*(B*‖J.val‖)+
        B*(‖nativeCollarCutoffCLM χ hχ‖*‖J.val‖) ≤ (1+L*B)*‖J.val‖
      calc
        _=L*B*‖J.val‖ := by dsimp only [L];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg J.val)

#print axioms nativeZeroPotentialCollarCLM_C2_ae
#print axioms nativeCutoffCommutatorCLM_C2_ae
#print axioms nativeCutoffCommutatorCLM_eq_density
#print axioms exists_native_cutoff_commutator_uniform_bound
end Yamabe3.Analysis.SpherePolar
