import Yamabe3.Analysis.NativeCollarL2SeriesIdentification
import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! The sum of the actual second weak jets has the same physical
Laplacian as the finite C2 modes, by comparison of actual strong L2 limits.
No fourth differentiability of the modes is required. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem nativeC2Collar_series_laplacian_eq_lift
    (u : AngularIndex → E → ℝ) (hu : ∀ i,ContDiffOn ℝ 2 (u i) ({0}ᶜ : Set E))
    (hs : ∀ j : Fin 3,Summable (fun i => nativeC2CollarSecond (hu i) j j))
    (U : ℝ → AngularL2) (hU : Continuous U)
    (hlap : ∀ s : Finset AngularIndex,∀ x : E,x≠0 →
      nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x=cylinderLift (projectedAngular s U) x)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t,(fun θ => w (t,θ))=ᵐ[angularVolume] (U t : S → ℝ)) :
    (⇑(∑ j : Fin 3,∑' i,nativeC2CollarSecond (hu i) j j))=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
  classical
  let v := fun i x => ∑ j : Fin 3,nativeCoordinateSecond j j (u i) x
  have hv (i : AngularIndex) : MemLp (v i) 2 (volume.restrict nativePoissonEntranceCollar) :=
    memLp_finsetSum Finset.univ (fun j _ => (nativeC2Collar_memLp (hu i)).2.2 j j)
  have he (i : AngularIndex) : (hv i).toLp (v i)=∑ j : Fin 3,nativeC2CollarSecond (hu i) j j := by
    symm
    exact lp_finset_sum_toLp (fun j => nativeCoordinateSecond j j (u i))
      (fun j => (nativeC2Collar_memLp (hu i)).2.2 j j) Finset.univ (hv i)
  have hsum : Summable (fun i => (hv i).toLp (v i)) := by
    simp_rw [he]
    exact (hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hs j).hasSum)).summable
  have ht : (∑' i,(hv i).toLp (v i))=∑ j : Fin 3,∑' i,nativeC2CollarSecond (hu i) j j := by
    simp_rw [he]
    exact Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hs j)
  rw [←ht]
  apply nativeCollarL2Series_eq_lift v hv hsum U hU ?_ hw hae
  intro s
  filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
  have hx0 : x≠0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx)
  change (∑ i ∈ s,∑ j : Fin 3,nativeCoordinateSecond j j (u i) x)=_
  rw [Finset.sum_comm]
  calc
    _ = nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x := by
      change (∑ j : Fin 3,∑ i ∈ s,nativeCoordinateSecond j j (u i) x)=
        ∑ j : Fin 3,nativeCoordinateSecond j j (fun y => ∑ i ∈ s,u i y) x
      apply Finset.sum_congr rfl
      intro j hj
      exact (nativeCoordinateSecond_finite_sum s isClosed_singleton.isOpen_compl u
        (fun i _ => hu i) j j (by simpa using hx0)).symm
    _ = _ := hlap s x hx0

#print axioms nativeC2Collar_series_laplacian_eq_lift
end Yamabe3.Analysis.SpherePolar
