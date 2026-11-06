import Yamabe3.Analysis.NativeCollarWeakGreen
import Yamabe3.Analysis.NativeCollarGreenRegion
import Yamabe3.Analysis.NativeCollarTotalClassicalGreen

/-! The ball-side Green formula for the same H2 jet. The opposite normal
sign follows from actual volume decomposition; the sphere has zero volume,
which is used only to compare domains, never to restrict volume representatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic GreenMass.NativeGaussSphereArea

 theorem nativeCollarGreen_total_zero (g : RiemannianMetric 3 E)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    nativeCollarGreenRegionCLM univ MeasurableSet.univ g ψ hψ J.val=0 := by
  have he : (fun J : nativeCollarJetClosure => nativeCollarGreenRegionCLM univ MeasurableSet.univ g ψ hψ J.val)=
      (fun _ : nativeCollarJetClosure => (0:ℝ)) := by
    apply nativeC2CollarJetInclusion_dense.equalizer
      ((nativeCollarGreenRegionCLM univ MeasurableSet.univ g ψ hψ).continuous.comp continuous_subtype_val)
      continuous_const
    funext u
    change nativeCollarGreenRegionCLM univ MeasurableSet.univ g ψ hψ (nativeC2CollarJetLinear u)=0
    rw [nativeCollarGreenRegion_C2,inter_univ]
    exact native_collar_total_classical_green g u ψ hψ hc hs
  exact congrFun he J

 theorem nativeCollarGreen_volume_split (g : RiemannianMetric 3 E)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (J : NativeCollarJet) :
    nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ J+
      nativeCollarGreenVolumeCLM g ψ hψ J=
      nativeCollarGreenRegionCLM univ MeasurableSet.univ g ψ hψ J := by
  let H := fun x => ψ x*(nativeCollarDensityLaplacianCLM g J : E → ℝ) x+
    ∑ j : Fin 3,nativeCollarGradientTest g ψ j x*(J.2.1 j : E → ℝ) x
  have hi (φ : E → ℝ) (hφ : Continuous φ) (F : NativeCollarL2) :
      Integrable (fun x => φ x*(F : E → ℝ) x) (volume.restrict nativePoissonEntranceCollar) := by
    have hφ2 : MemLp φ 2 (volume.restrict nativePoissonEntranceCollar) :=
      native_memLp_two_of_continuousOn_precompact (nativePolarTimeWindow_open (1/2)).measurableSet
        (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) hφ.continuousOn
    exact hφ2.integrable_mul (Lp.memLp F)
  have hH : Integrable H (volume.restrict nativePoissonEntranceCollar) :=
    (hi ψ hψ.continuous _).add (integrable_finsetSum _ (fun j _ => hi _ (continuous_nativeCollarGradientTest g hψ j) _))
  have hn : ∀ᵐ x : E ∂volume, x∉sphere (0:E) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0:E) 1)
  have hset : (ball (0:E) 1)ᶜ =ᵐ[volume.restrict nativePoissonEntranceCollar] {x : E | 1<‖x‖} := by
    filter_upwards [ae_mono Measure.restrict_le_self hn] with x hx
    apply propext
    have hne : ‖x‖≠1 := by simpa only [mem_sphere,dist_zero_right] using hx
    change (x∉ball (0:E) 1) ↔ 1<‖x‖
    simp only [mem_ball,dist_zero_right,not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left hne.symm)
  have hsplit := integral_add_compl (μ := volume.restrict nativePoissonEntranceCollar)
    (s := ball (0:E) 1) isOpen_ball.measurableSet hH
  have hc := setIntegral_congr_set (f := H) hset
  rw [hc] at hsplit
  rw [nativeCollarGreenRegion_eq_integral,nativeCollarGreenVolume_eq_integral,nativeCollarGreenRegion_eq_integral,inter_univ]
  have hΩ : MeasurableSet nativePoissonEntranceCollar := (nativePolarTimeWindow_open (1/2)).measurableSet
  simpa only [Measure.restrict_restrict isOpen_ball.measurableSet,
    Measure.restrict_restrict (isOpen_lt continuous_const continuous_norm).measurableSet,inter_comm,H] using hsplit

 theorem nativeCollarWeakGreen_interior (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ J.val=
      nativeCollarNativeNormalPairCLM g ψ hψ.continuous J := by
  have h := nativeCollarGreen_volume_split g ψ hψ J.val
  rw [nativeCollarGreen_total_zero g ψ hψ hc hs J,nativeCollarWeakGreen g hGauss ψ hψ hc hs J] at h
  linarith only [h]

 theorem nativeCollarWeakGreen_interior_integral (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    (∫ x in nativePoissonEntranceCollar ∩ ball 0 1,
      ψ x*(nativeCollarDensityLaplacianCLM g J.val : E → ℝ) x+
        ∑ j : Fin 3,nativeCollarGradientTest g ψ j x*(J.val.2.1 j : E → ℝ) x)=
      ∫ θ : S,ψ (θ:E)*(nativeCollarNormalTraceCLM J : S → ℝ) θ
        ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure := by
  rw [← nativeCollarGreenRegion_eq_integral (ball 0 1) isOpen_ball.measurableSet g ψ hψ J.val,
    nativeCollarWeakGreen_interior g hGauss ψ hψ hc hs J,
    nativeCollarNativeNormalPair_eq_integral g (fun θ v => hGauss θ v)]

#print axioms nativeCollarGreen_total_zero
#print axioms nativeCollarGreen_volume_split
#print axioms nativeCollarWeakGreen_interior
#print axioms nativeCollarWeakGreen_interior_integral
end Yamabe3.Analysis.SpherePolar
