import Yamabe3.Analysis.NativeC2CollarValueLinear
import Yamabe3.Analysis.L2WeakDerivativeLinear

/-! The genuine strong H2 jet closure of off-origin C2 functions on the
fixed collar. It records actual value, first and second volume L2 classes;
it does not assert an unproved density theorem for every Sobolev function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

abbrev NativeCollarL2 := Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)
abbrev NativeCollarJet := NativeCollarL2 × (Fin 3 → NativeCollarL2) × (Fin 3 → Fin 3 → NativeCollarL2)

def nativeC2OffZero : Submodule ℝ (E → ℝ) where
  carrier := {u | ContDiffOn ℝ 2 u ({0}ᶜ : Set E)}
  zero_mem' := contDiffOn_const
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun c u hu => hu.const_smul c

def nativeC2ValueLinear : nativeC2OffZero →ₗ[ℝ] NativeCollarL2 where
  toFun u := nativeC2CollarValue u.property
  map_add' u v := nativeC2CollarValue_add u.property v.property (u+v).property rfl
  map_smul' c u := nativeC2CollarValue_smul u.property (c • u).property c rfl

def nativeC2FirstLinear (j : Fin 3) : nativeC2OffZero →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) j nativeC2ValueLinear
    (fun u => nativeC2CollarFirst u.property j) (fun u => (nativeC2Collar_weak_jets u.property).1 j)

def nativeC2SecondLinear (k j : Fin 3) : nativeC2OffZero →ₗ[ℝ] NativeCollarL2 :=
  nativeL2WeakDerivativeLinearMap (nativePolarTimeWindow_open (1/2)) k (nativeC2FirstLinear j)
    (fun u => nativeC2CollarSecond u.property k j) (fun u => (nativeC2Collar_weak_jets u.property).2 k j)

def nativeC2CollarJetLinear : nativeC2OffZero →ₗ[ℝ] NativeCollarJet :=
  nativeC2ValueLinear.prod ((LinearMap.pi nativeC2FirstLinear).prod
    (LinearMap.pi (fun k => LinearMap.pi (nativeC2SecondLinear k))))

def nativeCollarJetClosure : Submodule ℝ NativeCollarJet := nativeC2CollarJetLinear.range.topologicalClosure

def nativeC2CollarJetInclusion : nativeC2OffZero →ₗ[ℝ] nativeCollarJetClosure :=
  nativeC2CollarJetLinear.codRestrict nativeCollarJetClosure
    (fun u => nativeC2CollarJetLinear.range.le_topologicalClosure ⟨u,rfl⟩)

theorem nativeC2CollarJetInclusion_dense : DenseRange nativeC2CollarJetInclusion := by
  have h := ((denseRange_inclusion_iff (s := Set.range nativeC2CollarJetLinear)
    (t := closure (Set.range nativeC2CollarJetLinear)) subset_closure).2 subset_rfl).comp
      (Set.rangeFactorization_surjective.denseRange : DenseRange (Set.rangeFactorization nativeC2CollarJetLinear))
      (continuous_inclusion subset_closure)
  exact h

theorem nativeCollarJetClosure_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → nativeC2OffZero} {J : NativeCollarJet}
    (hJ : Tendsto (fun a => nativeC2CollarJetLinear (u a)) l (𝓝 J)) : J ∈ nativeCollarJetClosure := by
  exact mem_closure_of_tendsto hJ (Eventually.of_forall fun a => ⟨u a,rfl⟩)

#print axioms nativeC2CollarJetLinear
#print axioms nativeC2CollarJetInclusion_dense
#print axioms nativeCollarJetClosure_of_tendsto
end Yamabe3.Analysis.SpherePolar
