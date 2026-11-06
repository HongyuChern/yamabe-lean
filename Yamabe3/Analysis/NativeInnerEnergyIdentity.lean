import Yamabe3.Analysis.NativeInnerEnergySeries
import Yamabe3.Analysis.NativeScaledCollarSameFunction
import Yamabe3.Analysis.NativeCollarDyadicShift
import Yamabe3.Analysis.L2LimitPointwiseIdentity

/-! The convergent energy series realizes the SAME inner field. Each
term is the actual scaled collar energy lift; its finite physical sums
telescope and their strong L2 limit is identified without restricting
AE statements to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
local notation "μe" => (RiemannianMetric.euclideanMetric 3).volumeMeasure
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem nativeInnerEnergySeries_same_function
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (J:ℕ→X →L[ℝ] nativeCollarJetClosure)
    {C:ℝ} (hC:0 ≤ C) (hJ:∀n:ℕ,‖J n‖ ≤ C)
    (u:X→E→ℝ)
    (he:∀n x,((J n x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(((n+1:ℕ):ℝ)/4)/2)*u x (Real.exp (-(((n+1:ℕ):ℝ)/4)) • y))
    (x:X) :
    (toL2 Deuc univ (nativeInnerEnergySeriesCLM (nativeCollarDyadicPiece χ)
      (nativeCollarDyadicPiece_smooth hχ) (nativeCollarDyadicPiece_compact hc)
      (nativeCollarDyadicPiece_support hs h1) J x):E→ℝ)=ᵐ[volume]
      fun y=>nativeCollarDyadicCutoff χ 1 y*u x y := by
  let δ:=nativeCollarDyadicPiece χ
  let hd:=nativeCollarDyadicPiece_smooth hχ
  let hdc:=nativeCollarDyadicPiece_compact hc
  let hds:=nativeCollarDyadicPiece_support hs h1
  let Z (N:ℕ):H1Zero Deuc univ:=∑n∈Finset.range N,nativeInnerEnergySeriesPiece δ hd hdc hds J n x
  let U:H1Zero Deuc univ:=nativeInnerEnergySeriesCLM δ hd hdc hds J x
  have hz:Tendsto (fun N=>toL2 Deuc univ (Z N)) atTop (𝓝 (toL2 Deuc univ U)) :=
    (toL2 Deuc univ).continuous.continuousAt.tendsto.comp
      (nativeInnerEnergySeries_partial_tendsto δ hd hdc hds J hC hJ x)
  let v (N:ℕ)(y:E):ℝ:=(∑n∈Finset.range N,δ (Real.exp (((n+1:ℕ):ℝ)/4) • y))*u x y
  have hpiece (n:ℕ):
      (toL2 Deuc univ (nativeInnerEnergySeriesPiece δ hd hdc hds J n x):E→ℝ)=ᵐ[μe]
        fun y=>δ (Real.exp (((n+1:ℕ):ℝ)/4) • y)*u x y := by
    dsimp only [nativeInnerEnergySeriesPiece,ContinuousLinearMap.comp_apply]
    simpa only [native_euclideanMetric_volumeMeasure] using
      nativeScaledCollarEnergyCLM_same_function δ hd hdc hds (((n+1:ℕ):ℝ)/4)
        (by positivity) (J n x) (u x) (he n x)
  have hrep (N:ℕ):v N=ᵐ[μe](toL2 Deuc univ (Z N):E→ℝ) := by
    have hall:=ae_all_iff.mpr hpiece
    have hm:toL2 Deuc univ (Z N)=∑n∈Finset.range N,toL2 Deuc univ (nativeInnerEnergySeriesPiece δ hd hdc hds J n x) := map_sum _ _ _
    rw [hm]
    filter_upwards [hall,Lp.coeFn_fun_finsetSum (Finset.range N)
      (fun n=>toL2 Deuc univ (nativeInnerEnergySeriesPiece δ hd hdc hds J n x))] with y hy hsum
    rw [hsum]
    change _=∑n∈Finset.range N,_
    simp only [hy,←Finset.sum_mul]
    rfl
  have hp:∀ᵐy∂μe,Tendsto (fun N=>v N y) atTop (𝓝 (nativeCollarDyadicCutoff χ 1 y*u x y)) := by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (volume.ae_ne (0:E)).mono (fun y hy=>(nativeCollarDyadicPiece_tendsto_sum_shift hs 1 hy).mul_const (u x y))
  have hout: (fun y=>nativeCollarDyadicCutoff χ 1 y*u x y)=ᵐ[μe](toL2 Deuc univ U:E→ℝ) :=
    ae_eq_of_tendsto_Lp_of_ae_pointwise _ _ hz v _ hrep hp
  simpa only [native_euclideanMetric_volumeMeasure] using hout.symm

#print axioms nativeInnerEnergySeries_same_function
end Yamabe3.Analysis.SpherePolar
