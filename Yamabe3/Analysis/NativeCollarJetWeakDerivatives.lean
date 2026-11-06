import Yamabe3.Analysis.NativeCollarJetPerturbation
import Yamabe3.Analysis.WeakGeometricPerturbation

/-! Every constructed strong C2 jet limit is an actual H2 function with
those same weak derivatives. Coefficient operators therefore represent
real weak second-order operators, not independent formal jet variables. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeCollarJetClosure_weak_jets (J : nativeCollarJetClosure) :
    (∀ j,HasWeakPartialDeriv j (J.val.2.1 j) J.val.1 nativePoissonEntranceCollar) ∧
    (∀ i j,HasWeakPartialDeriv i (J.val.2.2 i j) (J.val.2.1 j) nativePoissonEntranceCollar) := by
  constructor
  · intro j
    have hc := (native_weakPartial_Lp_graph_closed (Ω := nativePoissonEntranceCollar) j).preimage
      (nativeCollarJetValueCLM.continuous.prodMk (nativeCollarJetFirstCLM j).continuous)
    apply closure_minimal (s := Set.range nativeC2CollarJetLinear) ?_ hc J.property
    rintro Y ⟨u,rfl⟩
    exact (nativeC2Collar_weak_jets u.property).1 j
  · intro i j
    have hc := (native_weakPartial_Lp_graph_closed (Ω := nativePoissonEntranceCollar) i).preimage
      ((nativeCollarJetFirstCLM j).continuous.prodMk (nativeCollarJetSecondCLM i j).continuous)
    apply closure_minimal (s := Set.range nativeC2CollarJetLinear) ?_ hc J.property
    rintro Y ⟨u,rfl⟩
    exact (nativeC2Collar_weak_jets u.property).2 i j

theorem nativeCollarJetClosure_memH2 (J : nativeCollarJetClosure) :
    MemWkp 2 2 (J.val.1 : E → ℝ) nativePoissonEntranceCollar := by
  have h := nativeCollarJetClosure_weak_jets J
  apply memWkp_succ_of_weakDerivatives (nativePolarTimeWindow_open (1/2)) (by norm_num : (1:ℝ≥0∞)≤2)
    (Lp.memLp _) (g := fun j => J.val.2.1 j)
  · intro j
    apply MemWkp.one_iff_memW1p.mpr
    exact ⟨Lp.memLp _,fun i => ⟨_,Lp.memLp _,h.2 i j⟩⟩
  · exact h.1

theorem nativeCollarJetClosure_chosen_jets (J : nativeCollarJetClosure) :
    (∀ j,chosenWeakPartial' 2 j J.val.1 nativePoissonEntranceCollar =ᵐ[volume.restrict nativePoissonEntranceCollar]
      (J.val.2.1 j : E → ℝ)) ∧
    (∀ i j,chosenWeakPartial' 2 i (chosenWeakPartial' 2 j J.val.1 nativePoissonEntranceCollar)
      nativePoissonEntranceCollar =ᵐ[volume.restrict nativePoissonEntranceCollar] (J.val.2.2 i j : E → ℝ)) := by
  have hO := nativePolarTimeWindow_open (1/2)
  have hm := nativeCollarJetClosure_memH2 J
  have hw := nativeCollarJetClosure_weak_jets J
  have hf (j : Fin 3) : chosenWeakPartial' 2 j J.val.1 nativePoissonEntranceCollar =ᵐ[volume.restrict nativePoissonEntranceCollar]
      (J.val.2.1 j : E → ℝ) :=
    (chosenWeakPartial'_isWeakPartial_of_mem hm.memW1p j).ae_eq hO (hw.1 j)
      ((chosenWeakPartial'_memLp_of_mem hm.memW1p j).locallyIntegrable (by norm_num))
      ((Lp.memLp _).locallyIntegrable (by norm_num))
  refine ⟨hf,fun i j => ?_⟩
  have hh := native_weakPartial_transfer_ae (hf j) (ae_eq_rfl : (J.val.2.2 i j : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] _) (hw.2 i j)
  exact (chosenWeakPartial'_isWeakPartial_of_mem (hm.chosenWeakPartial_mem j).memW1p i).ae_eq hO hh
    ((chosenWeakPartial'_memLp_of_mem (hm.chosenWeakPartial_mem j).memW1p i).locallyIntegrable (by norm_num))
    ((Lp.memLp _).locallyIntegrable (by norm_num))

theorem nativeCollarJetPerturbation_weak_ae
    (a : Fin 3 → Fin 3 → E → ℝ) (b : Fin 3 → E → ℝ) (c : E → ℝ)
    (ha : ∀ i j,Continuous (a i j)) (hb : ∀ j,Continuous (b j)) (hc : Continuous c)
    (J : nativeCollarJetClosure) :
    (nativeCollarJetPerturbationCLM a b c ha hb hc J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weakSecondOrderPerturbation nativePoissonEntranceCollar a b c J.val.1 := by
  have hj := nativeCollarJetClosure_chosen_jets J
  filter_upwards [nativeCollarJetPerturbationCLM_ae a b c ha hb hc J.val,
    eventually_all.mpr hj.1,eventually_all.mpr (fun i => eventually_all.mpr (hj.2 i))] with x he h1 h2
  rw [he]
  simp only [weakSecondOrderPerturbation,h1,h2]

#print axioms nativeCollarJetClosure_weak_jets
#print axioms nativeCollarJetClosure_memH2
#print axioms nativeCollarJetClosure_chosen_jets
#print axioms nativeCollarJetPerturbation_weak_ae
end Yamabe3.Analysis.SpherePolar
