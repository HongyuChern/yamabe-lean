import Yamabe3.Analysis.NativeCollarSeriesValueTrace
import Yamabe3.Analysis.NativeAngularHalfRegularity

/-! Re-express the constructed sphere L2 trace in the original angular
Hilbert space. Finite spectral budgets pass through dense source limits. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeTraceAngularCLM : Lp ℝ 2 angularVolume →L[ℝ] AngularL2 :=
  l2MeasureRestrictCLM (by rw [Measure.restrict_univ])

theorem nativeTraceAngularCLM_ae (f : Lp ℝ 2 angularVolume) :
    (nativeTraceAngularCLM f : S → ℝ)=ᵐ[angularVolume] (f : S → ℝ) := by
  have h : (nativeTraceAngularCLM f : S → ℝ)=ᵐ[angularVolume.restrict univ] (f : S → ℝ) :=
    l2MeasureRestrict_ae (by rw [Measure.restrict_univ]) f
  simpa only [Measure.restrict_univ] using h

theorem nativeTraceAngular_left_inverse (f : AngularL2) :
    nativeTraceAngularCLM (nativeAngularTraceCLM f)=f := by
  apply Lp.ext
  have h := (nativeTraceAngularCLM_ae (nativeAngularTraceCLM f)).trans (nativeAngularTraceCLM_ae f)
  simpa only [Measure.restrict_univ] using h

theorem nativeTraceAngular_right_inverse (f : Lp ℝ 2 angularVolume) :
    nativeAngularTraceCLM (nativeTraceAngularCLM f)=f := by
  apply Lp.ext
  exact (nativeAngularTraceCLM_ae (nativeTraceAngularCLM f)).trans (nativeTraceAngularCLM_ae f)

theorem nativeAngularSpectral_bound_of_dense
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (i : Y → X) (hi : DenseRange i) (T : X →L[ℝ] AngularL2) (s C : ℝ)
    (h : ∀ y,NativeAngularSpectralRegular s (T (i y)) ∧
      (∑' j,nativeAngularWeightedSquare s (T (i y)) j)≤C*‖i y‖^2)
    (x : X) :
    NativeAngularSpectralRegular s (T x) ∧
      (∑' j,nativeAngularWeightedSquare s (T x) j)≤C*‖x‖^2 := by
  have hb (S : Finset AngularIndex) :
      (∑ j ∈ S,nativeAngularWeightedSquare s (T x) j)≤C*‖x‖^2 := by
    have hc : IsClosed {x : X | (∑ j ∈ S,nativeAngularWeightedSquare s (T x) j)≤C*‖x‖^2} := by
      apply isClosed_le
      · apply continuous_finsetSum
        intro j hj
        unfold nativeAngularWeightedSquare
        fun_prop
      · fun_prop
    refine hi.induction_on x hc ?_
    intro y
    exact ((h y).1.sum_le_tsum S (fun j hj => sq_nonneg _)).trans (h y).2
  have hn : 0≤(fun j => nativeAngularWeightedSquare s (T x) j) := fun j => sq_nonneg _
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

#print axioms nativeTraceAngular_left_inverse
#print axioms nativeTraceAngular_right_inverse
#print axioms nativeAngularSpectral_bound_of_dense
end Yamabe3.Analysis.SpherePolar
