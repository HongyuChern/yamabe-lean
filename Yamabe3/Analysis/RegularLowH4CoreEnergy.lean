import Yamabe3.Analysis.H4GraphEnergyLift
import Yamabe3.Analysis.NativeIncomingCoreCutoff

/-! The SAME regular affine coordinates and decaying weighted H4 field
have one bounded compact energy realization for any actual core cutoff.
The low coordinates are retained. The bound is fixed before later
physical dilation or application to a native homogeneous field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Delaunay PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
  (hs:tsupport χ⊆ball (0:E) 3)
  (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))

def regularAffineCutoffLinear : RegularLowJet →ₗ[ℝ] (E→ℝ) where
  toFun z x:=χ x*regularAffineField z x
  map_add' z w:=by
    funext x
    simp only [regularAffineField,Prod.fst_add,Prod.snd_add,ContinuousLinearMap.add_apply,Pi.add_apply]
    ring
  map_smul' c z:=by
    funext x
    simp only [RingHom.id_apply]
    change χ x*(c*z.1+c*z.2 x)=c*(χ x*(z.1+z.2 x))
    ring

include hχ in
theorem regularAffineCutoffLinear_C1 (z:RegularLowJet) :
    ContDiff ℝ 1 (regularAffineCutoffLinear χ z) :=
  (hχ.of_le (by norm_num)).mul ((regularAffineField_smooth z).of_le (by norm_num))

theorem regularAffineCutoffLinear_eval_continuous (x:E) :
    Continuous (fun z:RegularLowJet=>regularAffineCutoffLinear χ z x) := by
  change Continuous (fun z:RegularLowJet=>χ x*(z.1+z.2 x))
  exact continuous_const.mul (continuous_fst.add ((ContinuousLinearMap.apply ℝ ℝ x).continuous.comp continuous_snd))

def regularAffineCoreEnergyCLM : RegularLowJet →L[ℝ] H1Zero Deuc (ball (0:E) 3) :=
  euclideanC1FamilyCLM (ball (0:E) 3) isOpen_ball (regularAffineCutoffLinear χ)
    (regularAffineCutoffLinear_C1 χ hχ) (fun _=>hc.mul_right)
    (fun _=>tsupport_mul_subset_left.trans hs) (regularAffineCutoffLinear_eval_continuous χ)

def regularWeightedCoreEnergyCLM : HalfEndPhysicalH4Graph →L[ℝ] H1Zero Deuc (ball (0:E) 3) :=
  euclideanC1FamilyCLM (ball (0:E) 3) isOpen_ball (H4CoreCutoffLinear χ)
    (H4CoreCutoffLinear_C1 hχ hs h1)
    (fun z=>(H4CoreCutoffLinear_support hc hs z).1)
    (fun z=>(H4CoreCutoffLinear_support hc hs z).2) (H4CoreCutoffLinear_eval_continuous χ)

def regularLowH4CoreEnergyCLM : RegularLowH4Space →L[ℝ] H1Zero Deuc (ball (0:E) 3) :=
  (regularAffineCoreEnergyCLM χ hχ hc hs).comp (ContinuousLinearMap.fst ℝ RegularLowJet HalfEndPhysicalH4Graph)+
    (regularWeightedCoreEnergyCLM χ hχ hc hs h1).comp (ContinuousLinearMap.snd ℝ RegularLowJet HalfEndPhysicalH4Graph)

theorem regularLowH4CoreEnergyCLM_ae (z:RegularLowH4Space) :
    (toL2 Deuc (ball (0:E) 3) (regularLowH4CoreEnergyCLM χ hχ hc hs h1 z):E→ℝ)=ᵐ[volume]
      fun x=>χ x*regularLowH4Field z x := by
  have ha:(toL2 Deuc (ball (0:E) 3) (regularAffineCoreEnergyCLM χ hχ hc hs z.1):E→ℝ)=ᵐ[volume]
      fun x=>χ x*regularAffineField z.1 x := by
    simpa only [native_euclideanMetric_volumeMeasure,regularAffineCoreEnergyCLM,regularAffineCutoffLinear,
      LinearMap.coe_mk,AddHom.coe_mk] using
      euclideanC1FamilyCLM_ae (ball (0:E) 3) isOpen_ball (regularAffineCutoffLinear χ)
        (regularAffineCutoffLinear_C1 χ hχ) (fun _=>hc.mul_right)
        (fun _=>tsupport_mul_subset_left.trans hs) (regularAffineCutoffLinear_eval_continuous χ) z.1
  have hh:(toL2 Deuc (ball (0:E) 3) (regularWeightedCoreEnergyCLM χ hχ hc hs h1 z.2):E→ℝ)=ᵐ[volume]
      fun x=>χ x*halfEndEntranceExtension (halfEndPhysicalH4GraphValue z.2) x := by
    simpa only [native_euclideanMetric_volumeMeasure,regularWeightedCoreEnergyCLM,H4CoreCutoffLinear,
      LinearMap.coe_mk,AddHom.coe_mk] using
      euclideanC1FamilyCLM_ae (ball (0:E) 3) isOpen_ball (H4CoreCutoffLinear χ)
        (H4CoreCutoffLinear_C1 hχ hs h1) (fun z=>(H4CoreCutoffLinear_support hc hs z).1)
        (fun z=>(H4CoreCutoffLinear_support hc hs z).2) (H4CoreCutoffLinear_eval_continuous χ) z.2
  have hsum:(toL2 Deuc (ball (0:E) 3) (regularLowH4CoreEnergyCLM χ hχ hc hs h1 z):E→ℝ)=ᵐ[volume]
      (toL2 Deuc (ball (0:E) 3) (regularAffineCoreEnergyCLM χ hχ hc hs z.1):E→ℝ)+
      (toL2 Deuc (ball (0:E) 3) (regularWeightedCoreEnergyCLM χ hχ hc hs h1 z.2):E→ℝ) := by
    change (toL2 Deuc (ball (0:E) 3)
      (regularAffineCoreEnergyCLM χ hχ hc hs z.1+regularWeightedCoreEnergyCLM χ hχ hc hs h1 z.2):E→ℝ)=ᵐ[volume]_
    rw [map_add]
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_add
      (toL2 Deuc (ball (0:E) 3) (regularAffineCoreEnergyCLM χ hχ hc hs z.1))
      (toL2 Deuc (ball (0:E) 3) (regularWeightedCoreEnergyCLM χ hχ hc hs h1 z.2))
  filter_upwards [ha,hh,hsum] with x ha hh hsum
  rw [hsum]
  simp only [Pi.add_apply,ha,hh,regularLowH4Field]
  ring

#print axioms regularAffineCutoffLinear_C1
#print axioms regularLowH4CoreEnergyCLM_ae
end Yamabe3.Analysis.UniformElliptic
