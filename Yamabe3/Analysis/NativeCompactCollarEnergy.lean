import Yamabe3.Analysis.NativeCollarJetMultiplier
import Yamabe3.Analysis.NativeC1CompactEnergyApproximation
import Yamabe3.Analysis.UniformElliptic.SmoothApproximationH1
import Mathlib.Analysis.Normed.Operator.Extend

/-! A compact smooth multiplier of an actual closed collar jet has a
bounded realization in the ORIGINAL Euclidean H1Zero completion. The
C2 dense construction and the H1 bound are proved before extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Elliptic
local notation "D" => nativeWeakEuclideanD
local notation "O" => nativePoissonEntranceCollar
variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆O)

include hχ hs in
private theorem cutoffProduct_C1 (u:nativeC2OffZero) : ContDiff ℝ 1 (fun x:E=>χ x*u.val x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx:x∈tsupport χ
  · have hxO:x∈O := hs hx
    have hx0:x≠0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hxO)
    exact (hχ.contDiffAt.of_le (by norm_num)).mul
      ((u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0)).of_le (by norm_num))
  · have he:(fun y:E=>χ y*u.val y)=ᶠ[𝓝 x](fun _=>0) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

include hχ hc hs in
private theorem cutoffProduct_H01 (u:nativeC2OffZero) : MemH01 (fun x:E=>χ x*u.val x) O :=
  native_C1_compact_memH01 (nativePolarTimeWindow_open (1/2))
    (cutoffProduct_C1 χ hχ hs u) (hc.mul_right) (tsupport_mul_subset_left.trans hs)

include hχ hc hs in
private theorem exists_cutoffProduct_element (u:nativeC2OffZero) :
    ∃z:H1Zero D O,(toL2 D O z:E→ℝ)=ᵐ[volume]fun x=>χ x*u.val x := by
  obtain ⟨z,hz⟩:=exists_nativeEuclideanH01_of_memH01 (nativePolarTimeWindow_open (1/2))
    (cutoffProduct_H01 χ hχ hc hs u)
  refine ⟨z,hz.trans (Eventually.of_forall fun x=>?_ )⟩
  change nativePoissonEntranceCollar.indicator (fun y:E=>χ y*u.val y) x=χ x*u.val x
  by_cases hx:x∈O
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h)),zero_mul]

def nativeC2CutoffEnergyElement (u:nativeC2OffZero) : H1Zero D O :=
  Classical.choose (exists_cutoffProduct_element χ hχ hc hs u)

theorem nativeC2CutoffEnergyElement_ae (u:nativeC2OffZero) :
    (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u):E→ℝ)=ᵐ[volume]fun x=>χ x*u.val x :=
  Classical.choose_spec (exists_cutoffProduct_element χ hχ hc hs u)

private theorem cutoffEnergy_ae_native (u:nativeC2OffZero) :
    (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u):E→ℝ)=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
      fun x=>χ x*u.val x := by
  simpa only [native_euclideanMetric_volumeMeasure] using nativeC2CutoffEnergyElement_ae χ hχ hc hs u

def nativeC2CutoffEnergyLinear : nativeC2OffZero →ₗ[ℝ] H1Zero D O where
  toFun:=nativeC2CutoffEnergyElement χ hχ hc hs
  map_add':=by
    intro u v
    apply toL2_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [cutoffEnergy_ae_native χ hχ hc hs (u+v),cutoffEnergy_ae_native χ hχ hc hs u,
      cutoffEnergy_ae_native χ hχ hc hs v,Lp.coeFn_add (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u))
        (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs v))] with x ha hu hv hsum
    rw [ha,hsum]
    change χ x*(u.val x+v.val x)=_
    simp only [Pi.add_apply,hu,hv,mul_add]
  map_smul':=by
    intro c u
    simp only [RingHom.id_apply]
    apply toL2_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [cutoffEnergy_ae_native χ hχ hc hs (c • u),cutoffEnergy_ae_native χ hχ hc hs u,
      Lp.coeFn_smul c (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u))] with x ha hu hsm
    rw [ha,hsm]
    change χ x*(c*u.val x)=_
    simp only [Pi.smul_apply,smul_eq_mul,hu]
    ring

theorem nativeC2CutoffEnergyElement_norm_sq (u:nativeC2OffZero) :
    ‖nativeC2CutoffEnergyElement χ hχ hc hs u‖^2=
      ‖(nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u)).1‖^2+
        ∑j:Fin 3,‖(nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u)).2.1 j‖^2 := by
  let φ:=fun x:E=>χ x*u.val x
  have hφ:ContDiff ℝ 1 φ := cutoffProduct_C1 χ hχ hs u
  have hφc:HasCompactSupport φ := hc.mul_right
  have hφH:=cutoffProduct_H01 χ hχ hc hs u
  have hd (j:Fin 3):MemLp (fun x=>fderiv ℝ φ x (EuclideanSpace.single j 1)) 2 (volume.restrict O) :=
    (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ (EuclideanSpace.single j 1))).restrict O
  have hwd (j:Fin 3):HasWeakPartialDeriv j (fun x=>fderiv ℝ φ x (EuclideanSpace.single j 1)) φ O :=
    native_hasWeakPartialDeriv_of_contDiffOn_one (nativePolarTimeWindow_open (1/2)) hφ.contDiffOn j
  have hz:(toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u):E→ℝ)=ᵐ[volume]nativePoissonEntranceCollar.indicator φ := by
    apply (nativeC2CutoffEnergyElement_ae χ hχ hc hs u).trans
    apply Eventually.of_forall
    intro x
    by_cases hx:x∈O
    · exact (indicator_of_mem hx φ).symm
    · rw [indicator_of_notMem hx]
      simpa only [zero_mul] using congrArg (fun t:ℝ=>t*u.val x) (image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h)))
  rw [nativeEuclidean_memH01_norm_sq (nativePolarTimeWindow_open (1/2)) hφH _ hd hwd _ hz,
    nativeCollarCutoffRawCLM_C2]
  have hv:=norm_toLp_sq_eq_integral_sq (nativeC2Collar_memLp (nativeC2Cutoff χ hχ u).property).1
  change ‖nativeC2CollarValue (nativeC2Cutoff χ hχ u).property‖^2=_ at hv
  have hp (j:Fin 3):‖nativeC2CollarFirst (nativeC2Cutoff χ hχ u).property j‖^2=
      ∫x in O,(fderiv ℝ φ x (EuclideanSpace.single j 1))^2 :=
    norm_toLp_sq_eq_integral_sq ((nativeC2Collar_memLp (nativeC2Cutoff χ hχ u).property).2.1 j)
  change (∫x in O,φ x^2)+(∑j:Fin 3,∫x in O,(fderiv ℝ φ x (EuclideanSpace.single j 1))^2)=
    ‖nativeC2CollarValue (nativeC2Cutoff χ hχ u).property‖^2+
      ∑j:Fin 3,‖nativeC2CollarFirst (nativeC2Cutoff χ hχ u).property j‖^2
  rw [hv]
  simp_rw [hp]
  rfl

theorem nativeC2CutoffEnergyElement_norm_le (u:nativeC2OffZero) :
    ‖nativeC2CutoffEnergyElement χ hχ hc hs u‖ ≤
      (2*‖nativeCollarCutoffRawCLM χ hχ‖)*‖nativeC2CollarJetInclusion u‖ := by
  let J:=nativeCollarCutoffRawCLM χ hχ (nativeC2CollarJetLinear u)
  have h0:‖J.1‖ ≤ ‖J‖ := norm_fst_le J
  have h1 (j:Fin 3):‖J.2.1 j‖ ≤ ‖J‖ :=
    (norm_le_pi_norm J.2.1 j).trans ((norm_fst_le J.2).trans (norm_snd_le J))
  have hn:‖nativeC2CutoffEnergyElement χ hχ hc hs u‖ ≤ 2*‖J‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [nativeC2CutoffEnergyElement_norm_sq]
    have hh0:=pow_le_pow_left₀ (norm_nonneg J.1) h0 2
    have hh1 (j:Fin 3):‖J.2.1 j‖^2 ≤ ‖J‖^2 := pow_le_pow_left₀ (norm_nonneg _) (h1 j) 2
    have hh:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin 3)))=>hh1 j)
    change ‖J.1‖^2+(∑j:Fin 3,‖J.2.1 j‖^2) ≤ _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hh
    nlinarith only [hh0,hh]
  apply (hn.trans (mul_le_mul_of_nonneg_left ((nativeCollarCutoffRawCLM χ hχ).le_opNorm _) (by norm_num:0 ≤ (2:ℝ)))).trans_eq
  change 2*(‖nativeCollarCutoffRawCLM χ hχ‖*‖nativeC2CollarJetLinear u‖)=
    (2*‖nativeCollarCutoffRawCLM χ hχ‖)*‖nativeC2CollarJetLinear u‖
  ring

def nativeCompactCollarEnergyCLM : nativeCollarJetClosure →L[ℝ] H1Zero D O :=
  (nativeC2CutoffEnergyLinear χ hχ hc hs).extendOfNorm nativeC2CollarJetInclusion

theorem nativeCompactCollarEnergyCLM_C2 (u:nativeC2OffZero) :
    nativeCompactCollarEnergyCLM χ hχ hc hs (nativeC2CollarJetInclusion u)=
      nativeC2CutoffEnergyElement χ hχ hc hs u :=
  LinearMap.extendOfNorm_eq nativeC2CollarJetInclusion_dense
    ⟨_,nativeC2CutoffEnergyElement_norm_le χ hχ hc hs⟩ u

theorem nativeCompactCollarEnergyCLM_norm : ‖nativeCompactCollarEnergyCLM χ hχ hc hs‖ ≤
    2*‖nativeCollarCutoffRawCLM χ hχ‖ :=
  LinearMap.opNorm_extendOfNorm_le nativeC2CollarJetInclusion_dense (by positivity)
    (nativeC2CutoffEnergyElement_norm_le χ hχ hc hs)

#print axioms nativeC2CutoffEnergyElement_ae
#print axioms nativeC2CutoffEnergyElement_norm_sq
#print axioms nativeC2CutoffEnergyElement_norm_le
#print axioms nativeCompactCollarEnergyCLM_C2
#print axioms nativeCompactCollarEnergyCLM_norm
end Yamabe3.Analysis.SpherePolar
