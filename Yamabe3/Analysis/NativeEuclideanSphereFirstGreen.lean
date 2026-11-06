import Yamabe3.Analysis.NativeSphereDensityGreenC2

/-! First-order integration by parts across the actual unit sphere. The
boundary factor is the value trace times its coordinate normal component. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeEuclidean_density (x : E) : (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity id x=1 := by
  change Real.sqrt (Matrix.of (fun i j : Fin 3 =>
    (RiemannianMetric.euclideanMetric 3).inner x
      (mfderiv (𝓡 3) (𝓡 3) id x (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) id x (EuclideanSpace.basisFun (Fin 3) ℝ j)))).det=1
  simp only [mfderiv_id]
  change Real.sqrt (Matrix.of (fun i j : Fin 3 =>
    inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))).det=1
  have hB : Matrix.of (fun i j : Fin 3 => inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j))=1 := by
    ext i j
    simpa only [Matrix.of_apply,Matrix.one_apply] using (EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite i j
  rw [hB,Matrix.det_one,Real.sqrt_one]

theorem nativeEuclidean_divergence_matrix (x : E) : nativeDivergenceMatrix (RiemannianMetric.euclideanMetric 3) x=1 := by
  have hc : (RiemannianMetric.euclideanMetric 3).pullbackCoefficients id x=innerSL ℝ := by
    ext v w
    change (RiemannianMetric.euclideanMetric 3).inner x (mfderiv (𝓡 3) (𝓡 3) id x v) (mfderiv (𝓡 3) (𝓡 3) id x w)=inner ℝ v w
    rw [mfderiv_id]
    rfl
  have hinv : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).IsInvertible := (RiemannianMetric.euclideanMetric 3).inner_isInvertible x
  have hb (j : Fin 3) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (EuclideanSpace.single j 1)=EuclideanSpace.proj j := by
    ext v
    simp [innerSL_apply_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.single_apply]
  have hd (j : Fin 3) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).inverse (EuclideanSpace.proj j)=EuclideanSpace.single j 1 := by
    rw [←hb j]
    exact hinv.inverse_apply_self _
  ext i j
  change (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity id x*
    EuclideanSpace.proj i (((RiemannianMetric.euclideanMetric 3).pullbackCoefficients id x).inverse (EuclideanSpace.proj j))=_
  rw [nativeEuclidean_density,one_mul,hc,hd]
  simp [Matrix.one_apply]

theorem native_coordinate_partial (i j : Fin 3) (x : E) :
    partialDeriv i (fun y : E => y j) x=if i=j then 1 else 0 := by
  change (fderiv ℝ (EuclideanSpace.proj j : E → ℝ) x) (EuclideanSpace.single i 1)=_
  rw [ContinuousLinearMap.fderiv]
  simp [Pi.single_apply,eq_comm]

theorem native_exterior_partial_integral {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (j : Fin 3) :
    (∫x in {y : E | 1<‖y‖},partialDeriv j ψ x)= -(∫θ : S,ψ (θ:E)*(θ:E) j ∂angularVolume) := by
  have hq : ContDiff ℝ 2 (fun x : E => x j) := (show E →L[ℝ] ℝ from EuclideanSpace.proj j).contDiff
  have hflux (x : E) (i : Fin 3) : matrixFlux (nativeDivergenceMatrix (RiemannianMetric.euclideanMetric 3))
      (fun k => partialDeriv k (fun y : E => y j)) i x=if i=j then 1 else 0 := by
    simp [matrixFlux,nativeEuclidean_divergence_matrix,Matrix.one_apply,native_coordinate_partial]
  have hzero (x : E) : principalSource (nativeDivergenceMatrix (RiemannianMetric.euclideanMetric 3)) (fun y : E => y j) x=0 := by
    have he (i : Fin 3) : matrixFlux (nativeDivergenceMatrix (RiemannianMetric.euclideanMetric 3))
        (fun k => partialDeriv k (fun y : E => y j)) i=(fun _ => if i=j then (1:ℝ) else 0) := funext (fun x => hflux x i)
    simp only [principalSource,he,partialDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,Finset.sum_const_zero,neg_zero]
  have hd (x v : E) : (fderiv ℝ (fun y : E => y j) x) v=v j := by
    change (fderiv ℝ (EuclideanSpace.proj j : E → ℝ) x) v=_
    rw [ContinuousLinearMap.fderiv]
    rfl
  have h := native_exterior_density_green_C2 (RiemannianMetric.euclideanMetric 3) (fun _ _ => rfl) hq hψ hc
  simpa only [hzero,neg_zero,mul_zero,zero_add,hflux,nativeEuclidean_density,one_mul,
    hd,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

#print axioms nativeEuclidean_density
#print axioms nativeEuclidean_divergence_matrix
#print axioms native_coordinate_partial
#print axioms native_exterior_partial_integral
end Yamabe3.Analysis.SpherePolar
