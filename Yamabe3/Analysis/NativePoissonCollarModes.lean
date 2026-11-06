import Yamabe3.Analysis.NativePoissonFiniteH2Collar
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

def nativePoissonCollarMode (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) : E → ℝ :=
  nativePoissonFiniteCollar P b {i}
def nativePoissonEntranceCollar : Set E := nativePolarTimeWindow (Ioo (-(1/2:ℝ)) (1/2))

theorem nativePoissonCollarMode_C2 (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativePoissonCollarMode P b i) ({0}ᶜ : Set E) :=
  (nativePoissonFiniteCollar_finite_energy P b {i}).1

theorem nativePoissonCollarMode_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun x => ∑ i ∈ s,nativePoissonCollarMode P b i x) = nativePoissonFiniteCollar P b s := by
  funext x
  simp [nativePoissonCollarMode,nativePoissonFiniteCollar,finitePhysical]

theorem nativePoissonCollarMode_first_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) (j : Fin 3) {x : E} (hx : x ≠ 0) :
    (∑ i ∈ s,nativeCoordinateFirst j (nativePoissonCollarMode P b i) x) =
      nativeCoordinateFirst j (nativePoissonFiniteCollar P b s) x := by
  rw [← nativePoissonCollarMode_sum P b s]
  exact (nativeCoordinateFirst_finite_sum s isClosed_singleton.isOpen_compl _
    (fun i _ => nativePoissonCollarMode_C2 P b i) j hx).symm

theorem nativePoissonCollarMode_second_sum (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) (k j : Fin 3) {x : E} (hx : x ≠ 0) :
    (∑ i ∈ s,nativeCoordinateSecond k j (nativePoissonCollarMode P b i) x) =
      nativeCoordinateSecond k j (nativePoissonFiniteCollar P b s) x := by
  rw [← nativePoissonCollarMode_sum P b s]
  exact (nativeCoordinateSecond_finite_sum s isClosed_singleton.isOpen_compl _
    (fun i _ => nativePoissonCollarMode_C2 P b i) k j hx).symm

theorem nativePoissonCollarMode_memLp (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    MemLp (nativePoissonCollarMode P b i) 2 (volume.restrict nativePoissonEntranceCollar) ∧
      (∀ j,MemLp (nativeCoordinateFirst j (nativePoissonCollarMode P b i)) 2
        (volume.restrict nativePoissonEntranceCollar)) ∧
      (∀ k j,MemLp (nativeCoordinateSecond k j (nativePoissonCollarMode P b i)) 2
        (volume.restrict nativePoissonEntranceCollar)) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV := nativePolarTimeWindow_open (1/2)
  have hVc := nativePolarTimeWindow_precompact (1/2)
  have hVO := nativePolarTimeWindow_closure_offZero (1/2)
  have hu := nativePoissonCollarMode_C2 P b i
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j (nativePoissonCollarMode P b i)) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  refine ⟨native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO hu.continuousOn,
    fun j => native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO (hp j).continuousOn,
    fun k j => ?_⟩
  exact native_C1_partials_memLp_on_precompact hO hV.measurableSet hVc hVO (hp j) k

def nativePoissonCollarValueMode (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  (nativePoissonCollarMode_memLp P b i).1.toLp (nativePoissonCollarMode P b i)
def nativePoissonCollarFirstMode (P : NativeHighPotential) (b : AngularH1) (j : Fin 3) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativePoissonCollarMode_memLp P b i).2.1 j).toLp (nativeCoordinateFirst j (nativePoissonCollarMode P b i))
def nativePoissonCollarSecondMode (P : NativeHighPotential) (b : AngularH1) (k j : Fin 3) (i : AngularIndex) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativePoissonCollarMode_memLp P b i).2.2 k j).toLp (nativeCoordinateSecond k j (nativePoissonCollarMode P b i))

#print axioms nativePoissonCollarMode_memLp
#print axioms nativePoissonCollarMode_second_sum
end Yamabe3.Analysis.SpherePolar
