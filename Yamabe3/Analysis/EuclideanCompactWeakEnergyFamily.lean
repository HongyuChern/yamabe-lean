import Yamabe3.Analysis.EuclideanH1L2ClosedGraphLift
import Yamabe3.Analysis.NativeCompactCollarEnergyIdentity
import PoincareLib.Analysis.Sobolev.Boundary.Localization.Sobolev
import PoincareLib.Analysis.Sobolev.Boundary.Approximation.Closure

/-! Actual compact localization of a weak H1 family, followed by a
bounded lift retaining the SAME L2 function. This applies in particular
to the genuinely matched interface jets. Compact Sobolev approximation,
not a zero-trace input, constructs each energy realization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
local notation "Deuc" => nativeWeakEuclideanD
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem exists_euclideanCompact_weak_energy_family
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (F:X →L[ℝ] NativeCollarL2) (u:X→E→ℝ)
    (hFu:∀x:X,(F x:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u x)
    (hu:∀x:X,MemW1p 2 (u x) nativePoissonEntranceCollar) :
    ∃L:X →L[ℝ] H1Zero Deuc univ,
      (∀x:X,(toL2 Deuc univ (L x):E→ℝ)=ᵐ[volume]fun y=>χ y*u x y) ∧
      ∀x:X,‖L x‖ ≤ ‖L‖*‖x‖ := by
  let O:=nativePoissonEntranceCollar
  have hO:IsOpen O := nativePolarTimeWindow_open (1/2)
  let A:=(l2ZeroExtendCLM O hO.measurableSet).comp ((nativeCollarScalarMulCLM χ hχ.continuous).comp F)
  let B:=(l2EqualMeasureCLM (native_euclideanMetric_volumeMeasure 3).symm).comp A
  have hAv (x:X):(A x:E→ℝ)=ᵐ[volume]fun y=>χ y*u x y := by
    have hm:(nativeCollarScalarMulCLM χ hχ.continuous (F x):E→ℝ)=ᵐ[volume.restrict O]
        fun y=>χ y*u x y :=
      (nativeCollarScalarMulCLM_ae χ hχ.continuous (F x)).trans ((EventuallyEq.refl _ _).mul (hFu x))
    have hi:O.indicator (nativeCollarScalarMulCLM χ hχ.continuous (F x):E→ℝ)=ᵐ[volume]
        O.indicator (fun y=>χ y*u x y) := (ae_eq_restrict_iff_indicator_ae_eq hO.measurableSet).mp hm
    apply ((l2ZeroExtend_ae O hO.measurableSet _).trans hi).trans
    apply Eventually.of_forall
    intro y
    by_cases hy:y∈O
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy]
      change 0=χ y*u x y
      rw [image_eq_zero_of_notMem_tsupport (fun h=>hy (hs h)),zero_mul]
  have hBv (x:X):(B x:E→ℝ)=ᵐ[volume]fun y=>χ y*u x y := by
    have hc:(B x:E→ℝ)=ᵐ[volume](A x:E→ℝ) := by
      dsimp only [B,ContinuousLinearMap.comp_apply]
      simpa only [native_euclideanMetric_volumeMeasure] using
        l2EqualMeasureCLM_ae (native_euclideanMetric_volumeMeasure 3).symm (A x)
    exact hc.trans (hAv x)
  have hB (x:X):∃z:H1Zero Deuc univ,toL2 Deuc univ z=B x := by
    have hmul:MemWkp 1 2 (fun y=>χ y*u x y) univ :=
      memWkp_mul_smooth_of_tsupport_subset 1 isOpen_univ hO
        (by simpa only [inter_univ] using (MemWkp.one_iff_memW1p.mpr (hu x))) hχ hc hs
    have hH:MemH01 (fun y=>χ y*u x y) univ := by
      simpa using memW01p_of_memW1p_of_tsupport_subset isOpen_univ (p:=2) (u:=fun y=>χ y*u x y) (by norm_num)
        (by simpa using (MemWkp.one_iff_memW1p.mp hmul)) (hc.mul_right) (subset_univ _)
    obtain ⟨z,hz⟩:=exists_nativeEuclideanH01_of_memH01 isOpen_univ hH
    have hz':(toL2 Deuc univ z:E→ℝ)=ᵐ[volume]fun y=>χ y*u x y := by simpa only [indicator_univ] using hz
    refine ⟨z,Lp.ext ?_⟩
    simpa only [native_euclideanMetric_volumeMeasure] using hz'.trans (hBv x).symm
  let L:=euclideanH1L2LiftCLM univ B hB
  refine ⟨L,?_,L.le_opNorm⟩
  intro x
  change (toL2 Deuc univ (euclideanH1L2LiftCLM univ B hB x):E→ℝ)=ᵐ[volume]_
  rw [euclideanH1L2LiftCLM_toL2]
  exact hBv x

#print axioms exists_euclideanCompact_weak_energy_family
end Yamabe3.Analysis.SpherePolar
