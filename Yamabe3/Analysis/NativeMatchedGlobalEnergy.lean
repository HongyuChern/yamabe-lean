import Yamabe3.Analysis.NativeFiniteOuterEnergy
import Yamabe3.Analysis.NativeInnerEnergyIdentity
import Yamabe3.Analysis.NativeMatchedCollarEnergy
import Yamabe3.Analysis.SupportMultiplierAe

/-! A bounded ORIGINAL H1 realization of the same matched physical
field: infinite inner collars, the genuinely value-matched interface,
and finite outer collars. The hypotheses here are explicit intermediate
jet certificates; actual model producers discharge them separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem nativeEuclidean_toL2_add_ae (z w:H1Zero Deuc univ) :
    (toL2 Deuc univ (z+w):E→ℝ)=ᵐ[volume]fun y=>toL2 Deuc univ z y+toL2 Deuc univ w y := by
  rw [map_add]
  simpa only [native_euclideanMetric_volumeMeasure,Filter.EventuallyEq,Pi.add_apply] using Lp.coeFn_add (toL2 Deuc univ z) (toL2 Deuc univ w)

variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem exists_nativeMatched_global_energy_family
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (N:ℕ) (J:ℕ→X →L[ℝ] nativeCollarJetClosure)
    (K:Fin N→X →L[ℝ] nativeCollarJetClosure)
    (Ji Ko:X →L[ℝ] nativeCollarJetClosure)
    {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C)
    (hv:∀x:X,nativeCollarValueTraceCLM (Ji x)=nativeCollarValueTraceCLM (Ko x))
    (ui uo:X→E→ℝ)
    (hi0:∀x:X,((Ji x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]ui x)
    (ho0:∀x:X,((Ko x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]uo x)
    (hi:∀n:ℕ,∀x:X,((J n x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(((n+1:ℕ):ℝ)/4)/2)*ui x (Real.exp (-(((n+1:ℕ):ℝ)/4)) • y))
    (ho:∀i:Fin N,∀x:X,((K i x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(-((i.val+2:ℕ):ℝ)/4)/2)*uo x (Real.exp (-(-((i.val+2:ℕ):ℝ)/4)) • y)) :
    ∃L:X →L[ℝ] H1Zero Deuc univ,∀x:X,
      (toL2 Deuc univ (L x):E→ℝ)=ᵐ[volume]
        fun y=>nativeOuterCollarCutoff χ (N+1) y*(ball (0:E) 1).piecewise (ui x) (uo x) y := by
  let δ:=nativeCollarDyadicPiece χ
  let hd:=nativeCollarDyadicPiece_smooth hχ
  let hdc:=nativeCollarDyadicPiece_compact hc
  let hds:=nativeCollarDyadicPiece_support hs h1
  let γ:=nativeInterfaceCutoff χ
  let Li:=nativeInnerEnergySeriesCLM δ hd hdc hds J
  obtain ⟨Lc,hLc,_⟩:=exists_nativeMatchedCollar_energy_family γ
    (nativeInterfaceCutoff_smooth hχ) (nativeInterfaceCutoff_compact hc)
    (nativeInterfaceCutoff_support hs h1) Ji Ko hv
  let Lo:=nativeFiniteOuterEnergyCLM χ hχ hc hds K
  refine ⟨Li+Lc+Lo,fun x=>?_⟩
  have hLi:(toL2 Deuc univ (Li x):E→ℝ)=ᵐ[volume]
      fun y=>nativeCollarDyadicCutoff χ 1 y*ui x y :=
    nativeInnerEnergySeries_same_function χ hχ hc hs h1 J hC hJ ui hi x
  have hglue:nativeCollarGluedFunction (Ji x).val.1 (Ko x).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (ball (0:E) 1).piecewise (ui x) (uo x) := by
    filter_upwards [hi0 x,ho0 x] with y hi ho
    by_cases hy:y∈ball (0:E) 1 <;> simp only [nativeCollarGluedFunction,piecewise,hy,ite_true,ite_false,hi,ho]
  have hLc':(toL2 Deuc univ (Lc x):E→ℝ)=ᵐ[volume]
      fun y=>γ y*(ball (0:E) 1).piecewise (ui x) (uo x) y :=
    (hLc x).trans (supported_mul_ae_of_restrict (nativePolarTimeWindow_open (1/2)).measurableSet γ
      (nativeInterfaceCutoff_support hs h1) hglue)
  have hLo:(toL2 Deuc univ (Lo x):E→ℝ)=ᵐ[volume]
      fun y=>∑n∈Finset.range N,δ (Real.exp (-((n+2:ℕ):ℝ)/4) • y)*uo x y := by
    apply (nativeFiniteOuterEnergyCLM_same_function χ hχ hc hds K uo ho x).trans
    apply Eventually.of_forall
    intro y
    exact Fin.sum_univ_eq_sum_range (fun n:ℕ=>δ (Real.exp (-((n+2:ℕ):ℝ)/4) • y)*uo x y) N
  have hsum1:=nativeEuclidean_toL2_add_ae (Li x) (Lc x)
  have hsum2:=nativeEuclidean_toL2_add_ae (Li x+Lc x) (Lo x)
  change (toL2 Deuc univ (Li x+Lc x+Lo x):E→ℝ)=ᵐ[volume]_
  filter_upwards [hLi,hLc',hLo,hsum1,hsum2] with y hi hc ho hsum1 hsum2
  rw [hsum2,hsum1,hi,hc,ho]
  exact nativeMatchedField_partition_identity hs h1 N (ui x) (uo x) y

#print axioms nativeEuclidean_toL2_add_ae
#print axioms exists_nativeMatched_global_energy_family
end Yamabe3.Analysis.SpherePolar
