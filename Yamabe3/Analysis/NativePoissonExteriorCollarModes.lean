import Yamabe3.Analysis.NativePoissonCollarModes
import Yamabe3.Analysis.NativePoissonExteriorH2Estimates
import Yamabe3.Analysis.NativeC2FiniteSum
import Yamabe3.Analysis.L2WeakSeries
import Yamabe3.Analysis.L2SquareNormBound

/-! One actual reflected physical mode and all its actual coordinate
partials on the entrance collar. Finite sums retain the original field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativePoissonExteriorCollarMode (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) : E → ℝ :=
  nativePoissonExteriorFiniteCollar P b {i}


theorem nativePoissonExteriorCollarMode_C2 (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativePoissonExteriorCollarMode P b i) ({0}ᶜ : Set E) :=
  (nativePoissonExteriorFiniteCollar_finite_energy P b {i}).1

theorem nativePoissonExteriorCollarMode_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun x => ∑ i ∈ s,nativePoissonExteriorCollarMode P b i x) = nativePoissonExteriorFiniteCollar P b s := by
  funext x
  simp [nativePoissonExteriorCollarMode,nativePoissonExteriorFiniteCollar,finitePhysical]

theorem nativePoissonExteriorCollarMode_first_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) (j : Fin 3) {x : E} (hx : x ≠ 0) :
    (∑ i ∈ s,nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i) x) =
      nativeCoordinateFirst j (nativePoissonExteriorFiniteCollar P b s) x := by
  rw [← nativePoissonExteriorCollarMode_sum P b s]
  exact (nativeCoordinateFirst_finite_sum s isClosed_singleton.isOpen_compl _
    (fun i _ => nativePoissonExteriorCollarMode_C2 P b i) j hx).symm

theorem nativePoissonExteriorCollarMode_second_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) (k j : Fin 3) {x : E} (hx : x ≠ 0) :
    (∑ i ∈ s,nativeCoordinateSecond k j (nativePoissonExteriorCollarMode P b i) x) =
      nativeCoordinateSecond k j (nativePoissonExteriorFiniteCollar P b s) x := by
  rw [← nativePoissonExteriorCollarMode_sum P b s]
  exact (nativeCoordinateSecond_finite_sum s isClosed_singleton.isOpen_compl _
    (fun i _ => nativePoissonExteriorCollarMode_C2 P b i) k j hx).symm

theorem nativePoissonExteriorCollarMode_memLp (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    MemLp (nativePoissonExteriorCollarMode P b i) 2 (volume.restrict nativePoissonEntranceCollar) ∧
      (∀ j,MemLp (nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i)) 2
        (volume.restrict nativePoissonEntranceCollar)) ∧
      (∀ k j,MemLp (nativeCoordinateSecond k j (nativePoissonExteriorCollarMode P b i)) 2
        (volume.restrict nativePoissonEntranceCollar)) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV := nativePolarTimeWindow_open (1/2)
  have hVc := nativePolarTimeWindow_precompact (1/2)
  have hVO := nativePolarTimeWindow_closure_offZero (1/2)
  have hu := nativePoissonExteriorCollarMode_C2 P b i
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i)) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  refine ⟨native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO hu.continuousOn,
    fun j => native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO (hp j).continuousOn,
    fun k j => ?_⟩
  exact native_C1_partials_memLp_on_precompact hO hV.measurableSet hVc hVO (hp j) k

def nativePoissonExteriorCollarValueMode (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativePoissonExteriorCollarMode_memLp P b i).1.toLp (nativePoissonExteriorCollarMode P b i)
def nativePoissonExteriorCollarFirstMode (P : NativeHighPotential) (b : AngularH1) (j : Fin 3) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativePoissonExteriorCollarMode_memLp P b i).2.1 j).toLp (nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i))
def nativePoissonExteriorCollarSecondMode (P : NativeHighPotential) (b : AngularH1) (k j : Fin 3) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativePoissonExteriorCollarMode_memLp P b i).2.2 k j).toLp (nativeCoordinateSecond k j (nativePoissonExteriorCollarMode P b i))

#print axioms nativePoissonExteriorCollarMode_memLp
#print axioms nativePoissonExteriorCollarMode_second_sum
end Yamabe3.Analysis.SpherePolar
