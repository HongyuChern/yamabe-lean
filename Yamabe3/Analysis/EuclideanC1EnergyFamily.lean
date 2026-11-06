import Yamabe3.Analysis.NativeC1CompactEnergyApproximation
import Yamabe3.Analysis.UniformElliptic.H4CanonicalLimit
import Mathlib.Analysis.Normed.Operator.Banach

/-! A pointwise-continuous LINEAR compact C1 family has a bounded
linear realization in the actual Euclidean H1Zero completion. Linearity
uses the proved L2 injectivity; continuity uses an actual closed graph,
not continuity of arbitrary L2 point evaluations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (O:Set E) (hO:IsOpen O) (P:X →ₗ[ℝ] (E→ℝ))
  (hP:∀x,ContDiff ℝ 1 (P x)) (hc:∀x,HasCompactSupport (P x))
  (hs:∀x,tsupport (P x)⊆O)
local notation "D" => nativeWeakEuclideanD

include hO hP hc hs in
theorem exists_euclidean_C1_family_element (x:X) :
    ∃z:H1Zero D O,(toL2 D O z:E→ℝ)=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] P x := by
  obtain ⟨z,hz⟩ := exists_nativeEuclideanH01_of_memH01 hO
    (native_C1_compact_memH01 hO (hP x) (hc x) (hs x))
  have hmask:O.indicator (P x)=P x := by
    funext y
    by_cases hy:y∈O
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy,image_eq_zero_of_notMem_tsupport (fun ht => hy (hs x ht))]
  exact ⟨z,by simpa only [native_euclideanMetric_volumeMeasure,hmask] using hz⟩

def euclideanC1FamilyElement (x:X) : H1Zero D O :=
  Classical.choose (exists_euclidean_C1_family_element O hO P hP hc hs x)

theorem euclideanC1FamilyElement_ae (x:X) :
    (toL2 D O (euclideanC1FamilyElement O hO P hP hc hs x):E→ℝ)=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] P x :=
  Classical.choose_spec (exists_euclidean_C1_family_element O hO P hP hc hs x)

def euclideanC1FamilyLinear : X →ₗ[ℝ] H1Zero D O where
  toFun := euclideanC1FamilyElement O hO P hP hc hs
  map_add' x y := by
    apply toL2_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [euclideanC1FamilyElement_ae O hO P hP hc hs (x+y),
      euclideanC1FamilyElement_ae O hO P hP hc hs x,
      euclideanC1FamilyElement_ae O hO P hP hc hs y,
      Lp.coeFn_add (toL2 D O (euclideanC1FamilyElement O hO P hP hc hs x))
        (toL2 D O (euclideanC1FamilyElement O hO P hP hc hs y))] with z hsum hx hy hadd
    rw [hsum,hadd]
    simp only [Pi.add_apply]
    rw [hx,hy]
    exact congrFun (P.map_add x y) z
  map_smul' c x := by
    apply toL2_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [euclideanC1FamilyElement_ae O hO P hP hc hs (c • x),
      euclideanC1FamilyElement_ae O hO P hP hc hs x,
      Lp.coeFn_smul c (toL2 D O (euclideanC1FamilyElement O hO P hP hc hs x))] with z hsm hx ha
    rw [hsm]
    simp only [RingHom.id_apply]
    rw [ha]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hx]
    exact congrFun (P.map_smul c x) z

variable [CompleteSpace X]

theorem euclideanC1FamilyLinear_continuous
    (hp:∀y:E,Continuous (fun x:X => P x y)) :
    Continuous (euclideanC1FamilyLinear O hO P hP hc hs) := by
  apply (euclideanC1FamilyLinear O hO P hP hc hs).continuous_of_seq_closed_graph
  intro x F W hx hW
  let L := euclideanC1FamilyLinear O hO P hP hc hs
  have hAE y : (toL2 D O (L y):E→ℝ)=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] P y :=
    euclideanC1FamilyElement_ae O hO P hP hc hs y
  have hLp y : MemLp (P y) 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure := (Lp.memLp (toL2 D O (L y))).ae_eq (hAE y)
  have hLW:Tendsto (fun n => toL2 D O (L (x n))) atTop (𝓝 (toL2 D O W)) :=
    (toL2 D O).continuous.continuousAt.tendsto.comp hW
  have ht:Tendsto (fun n => eLpNorm (fun y => P (x n) y-toL2 D O W y) 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure) atTop (𝓝 0) := by
    apply ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hLW).congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae ((hAE (x n)).mono fun y hy => by change toL2 D O (L (x n)) y-toL2 D O W y=P (x n) y-toL2 D O W y; rw [hy])
  have hpoint:∀ᵐy ∂(RiemannianMetric.euclideanMetric 3).volumeMeasure,Tendsto (fun n => P (x n) y) atTop (𝓝 (P F y)) :=
    Eventually.of_forall fun y => (hp y).continuousAt.tendsto.comp hx
  have hsame:P F=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] (toL2 D O W:E→ℝ) :=
    ae_eq_of_l2_limit_of_ae_pointwise_limit (fun n => (hLp (x n)).aestronglyMeasurable)
      (Lp.memLp (toL2 D O W)).aestronglyMeasurable ht hpoint
  apply toL2_injective
  exact Lp.ext ((hAE F).trans hsame).symm

def euclideanC1FamilyCLM (hp:∀y:E,Continuous (fun x:X => P x y)) : X →L[ℝ] H1Zero D O :=
  ⟨euclideanC1FamilyLinear O hO P hP hc hs,euclideanC1FamilyLinear_continuous O hO P hP hc hs hp⟩

theorem euclideanC1FamilyCLM_ae (hp:∀y:E,Continuous (fun x:X => P x y)) (x:X) :
    (toL2 D O (euclideanC1FamilyCLM O hO P hP hc hs hp x):E→ℝ)=ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure] P x :=
  euclideanC1FamilyElement_ae O hO P hP hc hs x

#print axioms exists_euclidean_C1_family_element
#print axioms euclideanC1FamilyLinear_continuous
#print axioms euclideanC1FamilyCLM_ae
end Yamabe3.Analysis.SpherePolar
