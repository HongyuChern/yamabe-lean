import Yamabe3.Analysis.NativeCompactCollarEnergyIdentity
import Yamabe3.Analysis.EuclideanCompletedDilation
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-! Actual energy realization of one physical small-scale jet piece.
The exp(3s/2) jet convention and true three-dimensional H1 dilation give
exp(-2s), with the same zero-extended physical value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
local notation "O" => nativePoissonEntranceCollar
variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆O)

def nativeScaledCollarEnergyCLM (s:ℝ) (hs0:0 ≤ s) :
    nativeCollarJetClosure →L[ℝ] H1Zero Deuc univ :=
  (Real.exp (-3*s/2):ℝ) • ((inclusion (D := Deuc) (subset_univ (euclideanDilatedDomain (Real.exp (-s)) O))).comp
    ((euclideanH1DilationCLM (Real.exp_pos (-s)) (Real.exp_le_one_iff.mpr (by linarith)) O).comp
      (nativeCompactCollarEnergyCLM χ hχ hc hs)))

theorem nativeScaledCollarEnergyCLM_norm (s:ℝ) (hs0:0 ≤ s) :
    ‖nativeScaledCollarEnergyCLM χ hχ hc hs s hs0‖ ≤
      (2*‖nativeCollarCutoffRawCLM χ hχ‖)*Real.exp (-2*s) := by
  apply (nativeScaledCollarEnergyCLM χ hχ hc hs s hs0).opNorm_le_bound (by positivity)
  intro J
  change ‖Real.exp (-3*s/2) • inclusion (D := Deuc) _
    (euclideanH1DilationCLM (Real.exp_pos (-s)) _ O (nativeCompactCollarEnergyCLM χ hχ hc hs J))‖ ≤ _
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,norm_inclusion]
  have hE:‖nativeCompactCollarEnergyCLM χ hχ hc hs J‖ ≤
      (2*‖nativeCollarCutoffRawCLM χ hχ‖)*‖J‖ :=
    (nativeCompactCollarEnergyCLM χ hχ hc hs).le_of_opNorm_le (nativeCompactCollarEnergyCLM_norm χ hχ hc hs) J
  have hD:=euclideanH1DilationCLM_norm_le (Real.exp_pos (-s))
    (Real.exp_le_one_iff.mpr (show -s ≤ 0 by linarith)) O (nativeCompactCollarEnergyCLM χ hχ hc hs J)
  apply (mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _))) (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_half]
  rw [show -2*s=(-3*s/2)+(-s/2) by ring,Real.exp_add]
  ring

theorem nativeScaledCollarEnergyCLM_ae (s:ℝ) (hs0:0 ≤ s) (J:nativeCollarJetClosure) :
    (toL2 Deuc univ (nativeScaledCollarEnergyCLM χ hχ hc hs s hs0 J):E→ℝ)=ᵐ[volume]
      fun x=>Real.exp (-3*s/2)*nativePoissonEntranceCollar.indicator
        (fun y=>χ y*(J.val.1:E→ℝ) y) (Real.exp s • x) := by
  let W:=nativeCompactCollarEnergyCLM χ hχ hc hs J
  let a:=Real.exp (-s)
  have ha:0 < a := Real.exp_pos _
  have ha1:a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE:(toL2 Deuc O W:E→ℝ)=ᵐ[volume]nativePoissonEntranceCollar.indicator
      (fun y=>χ y*(J.val.1:E→ℝ) y) := nativeCompactCollarEnergyCLM_ae χ hχ hc hs J
  have hd:∀ᵐx:E∂volume,toL2 Deuc O W (a⁻¹ • x)=nativePoissonEntranceCollar.indicator
      (fun y=>χ y*(J.val.1:E→ℝ) y) (a⁻¹ • x) := by
    simpa only [Filter.EventuallyEq,preimage_univ,Measure.restrict_univ] using ae_comp_dilation (inv_ne_zero ha.ne') (ae_restrict_of_ae (s:=univ) hE)
  have hr:(toL2 Deuc (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O W):E→ℝ)=ᵐ[volume]
      fun x:E=>toL2 Deuc O W (a⁻¹ • x) := by
    simpa only [native_euclideanMetric_volumeMeasure] using euclideanH1DilationCLM_ae ha ha1 O W
  have hm:((Real.exp (-3*s/2)) • toL2 Deuc (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O W):Lp ℝ 2
      (RiemannianMetric.euclideanMetric 3).volumeMeasure)=
      toL2 Deuc univ (nativeScaledCollarEnergyCLM χ hχ hc hs s hs0 J) := by
    simp only [nativeScaledCollarEnergyCLM,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_smul,toL2_inclusion,W,a]
  have hsm:∀ᵐx:E∂volume,((Real.exp (-3*s/2)) •
      toL2 Deuc (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O W):Lp ℝ 2
        (RiemannianMetric.euclideanMetric 3).volumeMeasure) x=
      Real.exp (-3*s/2)*toL2 Deuc (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O W) x := by
    simpa only [Filter.EventuallyEq,native_euclideanMetric_volumeMeasure,Pi.smul_apply,smul_eq_mul] using
      Lp.coeFn_smul (Real.exp (-3*s/2)) (toL2 Deuc (euclideanDilatedDomain a O) (euclideanH1DilationCLM ha ha1 O W))
  rw [hm] at hsm
  filter_upwards [hsm,hr,hd] with x hm hr hd
  rw [hm,hr,hd]
  have he:a⁻¹=Real.exp s := by dsimp only [a];rw [←Real.exp_neg,neg_neg]
  rw [he]

#print axioms nativeScaledCollarEnergyCLM_norm
#print axioms nativeScaledCollarEnergyCLM_ae
end Yamabe3.Analysis.SpherePolar
