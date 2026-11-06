import Yamabe3.Analysis.L2SetIndicator
import Yamabe3.Analysis.NativeCollarH1Gluing
import Yamabe3.Analysis.EuclideanCompactWeakEnergyFamily

/-! Equal actual value traces give a weak H1 function across the unit
sphere. Its compact localization is a bounded map into the original
completion, retaining the very same glued L2 function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def nativeCollarGluedValueCLM : (NativeCollarL2×NativeCollarL2) →L[ℝ] NativeCollarL2 :=
  (l2SetIndicatorCLM (ball (0:E) 1) isOpen_ball.measurableSet).comp (ContinuousLinearMap.fst ℝ _ _)+
    (l2SetIndicatorCLM (ball (0:E) 1)ᶜ isOpen_ball.measurableSet.compl).comp (ContinuousLinearMap.snd ℝ _ _)

theorem nativeCollarGluedValueCLM_ae (J K:NativeCollarL2) :
    (nativeCollarGluedValueCLM (J,K):E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeCollarGluedFunction J K := by
  have hj:=l2SetIndicatorCLM_ae (ball (0:E) 1) isOpen_ball.measurableSet J
  have hk:=l2SetIndicatorCLM_ae (ball (0:E) 1)ᶜ isOpen_ball.measurableSet.compl K
  have hs:=Lp.coeFn_add (l2SetIndicatorCLM (ball (0:E) 1) isOpen_ball.measurableSet J)
    (l2SetIndicatorCLM (ball (0:E) 1)ᶜ isOpen_ball.measurableSet.compl K)
  filter_upwards [hj,hk,hs] with x hj hk hs
  change ((l2SetIndicatorCLM (ball (0:E) 1) isOpen_ball.measurableSet J)+
    (l2SetIndicatorCLM (ball (0:E) 1)ᶜ isOpen_ball.measurableSet.compl K):NativeCollarL2) x=_
  rw [hs]
  simp only [Pi.add_apply]
  rw [hj,hk]
  by_cases hx:x∈ball (0:E) 1 <;> simp [nativeCollarGluedFunction,hx]

theorem exists_nativeMatchedCollar_energy_family
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆nativePoissonEntranceCollar)
    (J K:X →L[ℝ] nativeCollarJetClosure)
    (hv:∀x:X,nativeCollarValueTraceCLM (J x)=nativeCollarValueTraceCLM (K x)) :
    ∃L:X →L[ℝ] H1Zero Deuc univ,
      (∀x:X,(toL2 Deuc univ (L x):E→ℝ)=ᵐ[volume]
        fun y=>χ y*nativeCollarGluedFunction (J x).val.1 (K x).val.1 y) ∧
      ∀x:X,‖L x‖ ≤ ‖L‖*‖x‖ := by
  let v:=nativeCollarJetValueCLM.comp nativeCollarJetClosure.subtypeL
  let F:=nativeCollarGluedValueCLM.comp ((v.comp J).prod (v.comp K))
  exact exists_euclideanCompact_weak_energy_family χ hχ hc hs F
    (fun x=>nativeCollarGluedFunction (J x).val.1 (K x).val.1)
    (fun x=>nativeCollarGluedValueCLM_ae _ _)
    (fun x=>nativeCollarGluedFunction_memH1 (J x) (K x) (hv x))

#print axioms nativeCollarGluedValueCLM_ae
#print axioms exists_nativeMatchedCollar_energy_family
end Yamabe3.Analysis.SpherePolar
