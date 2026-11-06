import Yamabe3.Analysis.NativeShellWeightedPolar

/-! Weighted polar pairings for genuine L2 angular sources, with actual
joint representatives and integrability proofs. No sphere restriction of
a volume null-set identity is performed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeAngularJoint_pairing
    (F G : Lp AngularL2 2 (volume : Measure ℝ)) (t : ℝ) :
    (∫ θ : S,nativeAngularL2Joint F (t,θ)*nativeAngularL2Joint G (t,θ) ∂angularVolume)=
      inner ℝ (F t) (G t) := by
  rw [L2.inner_def,setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [nativeAngularL2Joint_ae F t,nativeAngularL2Joint_ae G t] with θ hF hG
  simp only [hF,hG,RCLike.inner_apply,conj_trivial]
  ring

theorem nativeShell_weighted_joint_pairing
    (F G : Lp AngularL2 2 (volume : Measure ℝ)) :
    (∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
      cylinderLift (nativeAngularL2Joint F) x*cylinderLift (nativeAngularL2Joint G) x)=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ (F t) (G t) := by
  let w := nativeAngularL2Joint F
  let z := nativeAngularL2Joint G
  let f := fun x => nativeShellSourceWeight x*cylinderLift w x*cylinderLift z x
  have hw := nativeAngularL2Joint_measurable F
  have hz := nativeAngularL2Joint_measurable G
  have hm : Measurable f := (nativeShellSourceWeight_measurable.mul
    (measurable_cylinderLift hw)).mul (measurable_cylinderLift hz)
  have hF := nativeL2CollarLift_eq_lift F hw (Eventually.of_forall (nativeAngularL2Joint_ae F))
  have hG := nativeL2CollarLift_eq_lift G hz (Eventually.of_forall (nativeAngularL2Joint_ae G))
  have hweight : MemLp (fun x => nativeShellSourceWeight x*cylinderLift w x) 2
      (volume.restrict nativePoissonEntranceCollar) := by
    apply (Lp.memLp (nativeShellSourceWeightCLM (nativeL2CollarLift F))).ae_eq
    filter_upwards [nativeShellSourceWeightCLM_ae (nativeL2CollarLift F),hF] with x hm hf
    exact hm.trans (congrArg (fun a => nativeShellSourceWeight x*a) hf)
  have hGp : MemLp (cylinderLift z) 2 (volume.restrict nativePoissonEntranceCollar) :=
    (Lp.memLp (nativeL2CollarLift G)).ae_eq hG
  have hi : IntegrableOn f nativePoissonEntranceCollar := hweight.integrable_mul hGp
  have hs : nativePoissonEntranceCollar.indicator f=f := by
    funext x
    by_cases hx : x∈nativePoissonEntranceCollar
    · exact indicator_of_mem hx _
    · have hD : x∉nativeSourceShell := fun h => hx (nativeSourceShell_subset_collar h)
      simp only [indicator_of_notMem hx,f,nativeShellSourceWeight,indicator_of_notMem hD,zero_mul]
  have hi' : Integrable f := by
    rw [←hs]
    exact (integrable_indicator_iff (nativePolarTimeWindow_open (1/2)).measurableSet).mpr hi
  have ht (t : ℝ) :
      (∫ θ : S,logCylinderWeight f (t,θ) ∂angularVolume)=
        (Ioc (-(1/4:ℝ)) (1/4)).indicator (fun t => inner ℝ (F t) (G t)) t := by
    simp only [f,nativeShell_weighted_lifts_polar]
    by_cases ht : t∈Ioc (-(1/4:ℝ)) (1/4)
    · simp only [indicator_of_mem ht]
      exact nativeAngularJoint_pairing F G t
    · simp only [indicator_of_notMem ht,integral_zero]
  calc
    _ = ∫ x : E,f x := by
      have hΩ : MeasurableSet nativePoissonEntranceCollar := (nativePolarTimeWindow_open (1/2)).measurableSet
      have h := integral_indicator (μ := volume) (f := f) hΩ
      rw [hs] at h
      exact h.symm
    _ = ∫ t : ℝ,∫ θ : S,logCylinderWeight f (t,θ) ∂angularVolume :=
      integral_euclidean_eq_cylinder hm hi'
    _ = ∫ t : ℝ,(Ioc (-(1/4:ℝ)) (1/4)).indicator (fun t => inner ℝ (F t) (G t)) t := by
      simp only [ht]
    _ = _ := integral_indicator measurableSet_Ioc

theorem nativeShell_weighted_lift_pairing
    (F G : Lp AngularL2 2 (volume : Measure ℝ)) :
    (∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
      (nativeL2CollarLiftCLM F : E → ℝ) x*(nativeL2CollarLiftCLM G : E → ℝ) x)=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ (F t) (G t) := by
  calc
    _ = ∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
        cylinderLift (nativeAngularL2Joint F) x*cylinderLift (nativeAngularL2Joint G) x := by
      apply integral_congr_ae
      filter_upwards [nativeL2CollarLift_eq_lift F (nativeAngularL2Joint_measurable F)
        (Eventually.of_forall (nativeAngularL2Joint_ae F)),
        nativeL2CollarLift_eq_lift G (nativeAngularL2Joint_measurable G)
        (Eventually.of_forall (nativeAngularL2Joint_ae G))] with x hf hg
      change nativeShellSourceWeight x*(nativeL2CollarLift F : E → ℝ) x*(nativeL2CollarLift G : E → ℝ) x=_
      rw [hf,hg]
    _ = _ := nativeShell_weighted_joint_pairing F G

#print axioms nativeAngularJoint_pairing
#print axioms nativeShell_weighted_joint_pairing
#print axioms nativeShell_weighted_lift_pairing
end Yamabe3.Analysis.SpherePolar
