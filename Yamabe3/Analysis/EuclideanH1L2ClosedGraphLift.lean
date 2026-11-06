import Yamabe3.Analysis.NativeWeakChartCompletion
import Mathlib.Analysis.Normed.Operator.Banach

/-! A complete linear source family with an actual H1 realization for
every input has a bounded realization, when its L2 class is already a
continuous linear map. No continuity of L2 point evaluation is assumed.
The existence premise must be discharged by a genuine producer. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "μ" => (RiemannianMetric.euclideanMetric 3).volumeMeasure
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (O:Set E) (F:X →L[ℝ] Lp ℝ 2 μ) (hF:∀x:X,∃z:H1Zero D O,toL2 D O z=F x)

def euclideanH1L2LiftElement (x:X):H1Zero D O := (hF x).choose

theorem euclideanH1L2LiftElement_toL2 (x:X):toL2 D O (euclideanH1L2LiftElement O F hF x)=F x :=
  (hF x).choose_spec

def euclideanH1L2LiftLinear : X →ₗ[ℝ] H1Zero D O where
  toFun:=euclideanH1L2LiftElement O F hF
  map_add':=fun x y=>by
    apply toL2_injective
    rw [map_add,euclideanH1L2LiftElement_toL2,euclideanH1L2LiftElement_toL2,euclideanH1L2LiftElement_toL2,map_add]
  map_smul':=fun c x=>by
    simp only [RingHom.id_apply]
    apply toL2_injective
    rw [map_smul,euclideanH1L2LiftElement_toL2,euclideanH1L2LiftElement_toL2,map_smul]

theorem euclideanH1L2LiftLinear_continuous : Continuous (euclideanH1L2LiftLinear O F hF) := by
  apply (euclideanH1L2LiftLinear O F hF).continuous_of_seq_closed_graph
  intro xs x z hx hz
  apply toL2_injective
  change toL2 D O z=toL2 D O (euclideanH1L2LiftElement O F hF x)
  rw [euclideanH1L2LiftElement_toL2]
  have h1:=((toL2 D O).continuous.continuousAt.tendsto).comp hz
  change Tendsto (fun n=>toL2 D O (euclideanH1L2LiftElement O F hF (xs n))) atTop (𝓝 (toL2 D O z)) at h1
  simp only [euclideanH1L2LiftElement_toL2] at h1
  exact tendsto_nhds_unique h1 (F.continuous.continuousAt.tendsto.comp hx)

def euclideanH1L2LiftCLM : X →L[ℝ] H1Zero D O :=
  ⟨euclideanH1L2LiftLinear O F hF,euclideanH1L2LiftLinear_continuous O F hF⟩

theorem euclideanH1L2LiftCLM_toL2 (x:X):toL2 D O (euclideanH1L2LiftCLM O F hF x)=F x :=
  euclideanH1L2LiftElement_toL2 O F hF x

#print axioms euclideanH1L2LiftLinear_continuous
#print axioms euclideanH1L2LiftCLM_toL2
end Yamabe3.Analysis.SpherePolar
