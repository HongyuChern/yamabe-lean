import Yamabe3.Analysis.NativeCollarJetLimits
import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.L2MeasureRestriction

/-! Passing the actual scalar-potential equation through strong C2 jet
limits on a specified measurable part of the collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativeCollarSubsetRestrictionCLM (D : Set E) (hD : D ⊆ nativePoissonEntranceCollar) :
    NativeCollarL2 →L[ℝ] Lp ℝ 2 (volume.restrict D) :=
  l2MeasureRestrictCLM (Measure.restrict_mono hD le_rfl)

theorem nativeC2Collar_equation_zero (D : Set E) (hD : D ⊆ nativePoissonEntranceCollar)
    (hm : MeasurableSet D) (V : ℝ →ᵇ ℝ) (u : nativeC2OffZero)
    (heq : ∀ x ∈ D,nativeCoordinateLaplacian u.val x+nativeHalfEndPotentialCoefficient V x*u.val x=0) :
    nativeCollarSubsetRestrictionCLM D hD ((∑ j : Fin 3,nativeC2CollarSecond u.property j j)+
      nativeCollarPotentialMulCLM V (nativeC2CollarValue u.property))=0 := by
  let L := ∑ j : Fin 3,nativeC2CollarSecond u.property j j
  let U := nativeC2CollarValue u.property
  have hv := (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hs : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,∀ j : Fin 3,
      nativeC2CollarSecond u.property j j x=nativeCoordinateSecond j j u.val x :=
    (ae_all_iff).mpr (fun j => ((nativeC2Collar_memLp u.property).2.2 j j).coeFn_toLp)
  have hL : (L : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian u.val := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativeC2CollarSecond u.property j j),hs] with x hx hs
    change L x=_
    rw [hx]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hs j)
  have hμ : volume.restrict D ≤ volume.restrict nativePoissonEntranceCollar := Measure.restrict_mono hD le_rfl
  have hres : (⇑(L+nativeCollarPotentialMulCLM V U))=ᵐ[volume.restrict D] (fun _ => 0) := by
    filter_upwards [ae_mono hμ hv,ae_mono hμ hL,ae_mono hμ (nativeCollarPotentialMulCLM_ae V U),
      ae_mono hμ (Lp.coeFn_add L (nativeCollarPotentialMulCLM V U)),ae_restrict_mem hm] with x hv hL hV ha hx
    rw [ha]
    change L x+nativeCollarPotentialMulCLM V U x=0
    rw [hL,hV]
    have huv : U x=u.val x := hv
    rw [huv]
    exact heq x hx
  apply Lp.ext
  exact (l2MeasureRestrict_ae hμ _).trans (hres.trans (Lp.coeFn_zero ℝ 2 _).symm)

theorem nativeC2CollarSeries_equation_zero {ι : Type*}
    (D : Set E) (hD : D ⊆ nativePoissonEntranceCollar) (hm : MeasurableSet D)
    (V : ℝ →ᵇ ℝ) (u : ι → nativeC2OffZero)
    (hv : Summable (fun i => nativeC2CollarValue (u i).property))
    (hs : ∀ k j,Summable (fun i => nativeC2CollarSecond (u i).property k j))
    (heq : ∀ i x,x ∈ D → nativeCoordinateLaplacian (u i).val x+
      nativeHalfEndPotentialCoefficient V x*(u i).val x=0) :
    nativeCollarSubsetRestrictionCLM D hD
      ((∑ j : Fin 3,∑' i,nativeC2CollarSecond (u i).property j j)+
        nativeCollarPotentialMulCLM V (∑' i,nativeC2CollarValue (u i).property))=0 := by
  have hd : Summable (fun i => ∑ j : Fin 3,nativeC2CollarSecond (u i).property j j) :=
    (hasSum_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => (hs j j).hasSum)).summable
  have he := Summable.tsum_finsetSum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => hs j j)
  rw [←he,(nativeCollarPotentialMulCLM V).map_tsum hv,
    ←Summable.tsum_add hd ((nativeCollarPotentialMulCLM V).summable hv),
    (nativeCollarSubsetRestrictionCLM D hD).map_tsum (hd.add ((nativeCollarPotentialMulCLM V).summable hv))]
  simp_rw [nativeC2Collar_equation_zero D hD hm V _ (heq _)]
  exact tsum_zero

#print axioms nativeC2Collar_equation_zero
#print axioms nativeC2CollarSeries_equation_zero
end Yamabe3.Analysis.SpherePolar
