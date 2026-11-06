import Yamabe3.Analysis.NativeArbitraryScaledCollarEnergy

/-! One weighted jet represents one physical function: its constructed
energy piece is exactly the same cutoff function in full volume. The
restricted AE relation is extended and dilated before use. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem nativeArbitraryScaledCollarEnergyCLM_same_function
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (s:ℝ) (J:nativeCollarJetClosure) (u:E→ℝ)
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y)) :
    (toL2 Deuc univ (nativeArbitraryScaledCollarEnergyCLM χ hχ hc hs s J):E→ℝ)=ᵐ[volume]
      fun x=>χ (Real.exp s • x)*u x := by
  have hind:nativePoissonEntranceCollar.indicator (fun y=>χ y*(J.val.1:E→ℝ) y)=ᵐ[volume]
      nativePoissonEntranceCollar.indicator (fun y=>χ y*(Real.exp (3*s/2)*u (Real.exp (-s) • y))) :=
    (ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp
      ((EventuallyEq.refl _ _).mul hJ)
  have hd:(fun x:E=>nativePoissonEntranceCollar.indicator (fun y=>χ y*(J.val.1:E→ℝ) y) (Real.exp s • x))=ᵐ[volume]
      fun x=>nativePoissonEntranceCollar.indicator
        (fun y=>χ y*(Real.exp (3*s/2)*u (Real.exp (-s) • y))) (Real.exp s • x) := by
    simpa only [preimage_univ,Measure.restrict_univ] using
      ae_comp_dilation (Real.exp_ne_zero s) (ae_restrict_of_ae (s:=univ) hind)
  filter_upwards [nativeArbitraryScaledCollarEnergyCLM_ae χ hχ hc hs s J,hd] with x hE hd
  rw [hE,hd]
  by_cases hx:Real.exp s • x∈nativePoissonEntranceCollar
  · rw [indicator_of_mem hx]
    have he:Real.exp (-s) • (Real.exp s • x)=x := by rw [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
    rw [he]
    have hh:Real.exp (-3*s/2)*Real.exp (3*s/2)=1 := by
      rw [←Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    calc
      _=(Real.exp (-3*s/2)*Real.exp (3*s/2))*(χ (Real.exp s • x)*u x) := by ring
      _=_ := by rw [hh,one_mul]
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h)),zero_mul,mul_zero]

#print axioms nativeArbitraryScaledCollarEnergyCLM_same_function
end Yamabe3.Analysis.SpherePolar
