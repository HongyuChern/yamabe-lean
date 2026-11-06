import Yamabe3.Analysis.NativeCollarJetWeakDerivatives

/-! The actual strong H2 jet closure has no independent derivative
variables: equality of the volume L2 value fixes both weak derivative rows. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeCollarJet_value_injective : Function.Injective (fun J : nativeCollarJetClosure => J.val.1) := by
  intro J K he
  change J.val.1=K.val.1 at he
  have hJ := nativeCollarJetClosure_weak_jets J
  have hK := nativeCollarJetClosure_weak_jets K
  have h1 (j : Fin 3) : J.val.2.1 j=K.val.2.1 j := by
    apply Lp.ext
    have h := hJ.1 j
    rw [he] at h
    exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (hK.1 j)
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
  have h2 (i j : Fin 3) : J.val.2.2 i j=K.val.2.2 i j := by
    apply Lp.ext
    have h := hJ.2 i j
    rw [h1 j] at h
    exact h.ae_eq (nativePolarTimeWindow_open (1/2)) (hK.2 i j)
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
  apply Subtype.ext
  exact Prod.ext he (Prod.ext (funext h1) (funext (fun i => funext (h2 i))))

#print axioms nativeCollarJet_value_injective
end Yamabe3.Analysis.SpherePolar
