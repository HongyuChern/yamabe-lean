import Yamabe3.Analysis.NativePoissonExteriorCollarSummability

/-! The infinite physical Poisson series on the entrance collar has one
actual H2 value class and strongly convergent first/second weak derivatives.
Identification with the original positive-time curve is a separate step. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativePoissonExteriorCollarValue (P : NativeHighPotential) (b : AngularH1) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) := ∑' i,nativePoissonExteriorCollarValueMode P b i
def nativePoissonExteriorCollarFirst (P : NativeHighPotential) (b : AngularH1) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) := ∑' i,nativePoissonExteriorCollarFirstMode P b j i
def nativePoissonExteriorCollarSecond (P : NativeHighPotential) (b : AngularH1) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) := ∑' i,nativePoissonExteriorCollarSecondMode P b k j i

theorem nativePoissonExteriorCollarMode_weak_jets (P : NativeHighPotential) (b : AngularH1) (a : AngularIndex) :
    (∀ j,HasWeakPartialDeriv j (nativePoissonExteriorCollarFirstMode P b j a)
      (nativePoissonExteriorCollarValueMode P b a) nativePoissonEntranceCollar) ∧
    (∀ k j,HasWeakPartialDeriv k (nativePoissonExteriorCollarSecondMode P b k j a)
      (nativePoissonExteriorCollarFirstMode P b j a) nativePoissonEntranceCollar) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV : IsOpen nativePoissonEntranceCollar := nativePolarTimeWindow_open (1/2)
  have hVO : nativePoissonEntranceCollar ⊆ ({0}ᶜ : Set E) :=
    subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  have hu := nativePoissonExteriorCollarMode_C2 P b a
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b a)) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  constructor
  · intro j
    apply native_weakPartial_transfer_ae (nativePoissonExteriorCollarMode_memLp P b a).1.coeFn_toLp
      ((nativePoissonExteriorCollarMode_memLp P b a).2.1 j).coeFn_toLp
    exact native_hasWeakPartialDeriv_of_contDiffOn_one hV ((hu.of_le (by norm_num)).mono hVO) j
  · intro k j
    apply native_weakPartial_transfer_ae ((nativePoissonExteriorCollarMode_memLp P b a).2.1 j).coeFn_toLp
      ((nativePoissonExteriorCollarMode_memLp P b a).2.2 k j).coeFn_toLp
    exact native_hasWeakPartialDeriv_of_contDiffOn_one hV ((hp j).mono hVO) k

theorem nativePoissonExteriorCollar_H2_and_strong_jets (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    MemWkp 2 2 (nativePoissonExteriorCollarValue P b) nativePoissonEntranceCollar ∧
    (∀ j,HasWeakPartialDeriv j (nativePoissonExteriorCollarFirst P b j)
      (nativePoissonExteriorCollarValue P b) nativePoissonEntranceCollar) ∧
    (∀ k j,HasWeakPartialDeriv k (nativePoissonExteriorCollarSecond P b k j)
      (nativePoissonExteriorCollarFirst P b j) nativePoissonEntranceCollar) ∧
    Tendsto (fun s : Finset AngularIndex => ∑ i ∈ s,nativePoissonExteriorCollarValueMode P b i)
      atTop (𝓝 (nativePoissonExteriorCollarValue P b)) ∧
    (∀ j,Tendsto (fun s : Finset AngularIndex => ∑ i ∈ s,nativePoissonExteriorCollarFirstMode P b j i)
      atTop (𝓝 (nativePoissonExteriorCollarFirst P b j))) ∧
    (∀ k j,Tendsto (fun s : Finset AngularIndex => ∑ i ∈ s,nativePoissonExteriorCollarSecondMode P b k j i)
      atTop (𝓝 (nativePoissonExteriorCollarSecond P b k j))) := by
  have h := nativePoissonExteriorCollar_modes_summable P b hb
  have hw := native_memWkp_two_Lp_series (nativePolarTimeWindow_open (1/2))
    (nativePoissonExteriorCollarValueMode P b) (nativePoissonExteriorCollarFirstMode P b) (nativePoissonExteriorCollarSecondMode P b)
    h.1 h.2.1 h.2.2
    (fun a j => (nativePoissonExteriorCollarMode_weak_jets P b a).1 j)
    (fun a k j => (nativePoissonExteriorCollarMode_weak_jets P b a).2 k j)
  exact ⟨hw.1,hw.2.1,hw.2.2,h.1.hasSum,fun j => (h.2.1 j).hasSum,fun k j => (h.2.2 k j).hasSum⟩

#print axioms nativePoissonExteriorCollarMode_weak_jets
#print axioms nativePoissonExteriorCollar_H2_and_strong_jets
end Yamabe3.Analysis.SpherePolar
