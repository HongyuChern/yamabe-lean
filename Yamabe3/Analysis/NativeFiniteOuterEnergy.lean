import Yamabe3.Analysis.NativeArbitraryScaledCollarSameFunction
import Yamabe3.Analysis.NativeInterfaceCutoffPartition

/-! Actual finite outer collar energy operators. Every summand uses
the SAME source and same field, with its literal physical dilation.
The finite outer energy norm constant is fixed before its input. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem nativeEuclidean_toL2_finset_sum_ae {ι:Type*} (s:Finset ι) (z:ι→H1Zero Deuc univ) :
    (toL2 Deuc univ (∑i∈s,z i):E→ℝ)=ᵐ[volume]fun x=>∑i∈s,toL2 Deuc univ (z i) x := by
  rw [map_sum]
  simpa only [native_euclideanMetric_volumeMeasure] using Lp.coeFn_fun_finsetSum s (fun i=>toL2 Deuc univ (z i))

variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nativeFiniteOuterEnergyCLM
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport (nativeCollarDyadicPiece χ)⊆nativePoissonEntranceCollar)
    {N:ℕ} (K:Fin N→X →L[ℝ] nativeCollarJetClosure) : X →L[ℝ] H1Zero Deuc univ :=
  ∑i:Fin N,(nativeArbitraryScaledCollarEnergyCLM (nativeCollarDyadicPiece χ)
    (nativeCollarDyadicPiece_smooth hχ) (nativeCollarDyadicPiece_compact hc) hs (-((i.val+2:ℕ):ℝ)/4)).comp (K i)

theorem nativeFiniteOuterEnergyCLM_same_function
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport (nativeCollarDyadicPiece χ)⊆nativePoissonEntranceCollar)
    {N:ℕ} (K:Fin N→X →L[ℝ] nativeCollarJetClosure) (u:X→E→ℝ)
    (he:∀i:Fin N,∀x:X,((K i x).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(-((i.val+2:ℕ):ℝ)/4)/2)*u x (Real.exp (-(-((i.val+2:ℕ):ℝ)/4)) • y)) (x:X) :
    (toL2 Deuc univ (nativeFiniteOuterEnergyCLM χ hχ hc hs K x):E→ℝ)=ᵐ[volume]
      fun y=>(∑i:Fin N,nativeCollarDyadicPiece χ (Real.exp (-((i.val+2:ℕ):ℝ)/4) • y)*u x y) := by
  let Z (i:Fin N):H1Zero Deuc univ:=nativeArbitraryScaledCollarEnergyCLM (nativeCollarDyadicPiece χ)
    (nativeCollarDyadicPiece_smooth hχ) (nativeCollarDyadicPiece_compact hc) hs (-((i.val+2:ℕ):ℝ)/4) (K i x)
  have hZ (i:Fin N):(toL2 Deuc univ (Z i):E→ℝ)=ᵐ[volume]
      fun y=>nativeCollarDyadicPiece χ (Real.exp (-((i.val+2:ℕ):ℝ)/4) • y)*u x y :=
    nativeArbitraryScaledCollarEnergyCLM_same_function _ _ _ _ _ _ _ (he i x)
  have hsum:=nativeEuclidean_toL2_finset_sum_ae Finset.univ Z
  have hall:=ae_all_iff.mpr hZ
  have hcl:nativeFiniteOuterEnergyCLM χ hχ hc hs K x=∑i:Fin N,Z i := by
    simp only [nativeFiniteOuterEnergyCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,Z]
  rw [hcl]
  filter_upwards [hsum,hall] with y hsum hall
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _=>hall i)

#print axioms nativeEuclidean_toL2_finset_sum_ae
#print axioms nativeFiniteOuterEnergyCLM_same_function
end Yamabe3.Analysis.SpherePolar
