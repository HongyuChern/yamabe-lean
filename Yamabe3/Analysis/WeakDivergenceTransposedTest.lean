import Yamabe3.Analysis.WeakDivergenceSourceIdentity

/-! The actual variable-coefficient H2 divergence source has the
transposed smooth-test identity. One integration by parts uses the
actual chosen weak first partials; coefficient symmetry is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {d:ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakDivergenceSource_transposed_test {O:Set E} (hO:IsOpen O)
    (A:E→Matrix (Fin d) (Fin d) ℝ) (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j))
    (hsymm:∀x i j,A x i j=A x j i)
    {u:E→ℝ} (hu:MemWkp 2 2 u O)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (hs:tsupport φ⊆O) :
    (∫x in O,u x*principalSource A φ x)=∫x in O,weakDivergenceSource O A u x*φ x := by
  let p:=fun j=>chosenWeakPartial' 2 j u O
  let ψ:=matrixFlux A (fun i=>partialDeriv i φ)
  have hψ(j:Fin d):ContDiff ℝ ∞ (ψ j):=
    ContDiff.sum (fun i _=>(hA j i).mul (contDiff_partial hφ i))
  have hψs(j:Fin d):tsupport (ψ j)⊆tsupport φ:=by
    intro x hx
    by_contra hn
    have he:ψ j=ᶠ[𝓝 x](fun _=>0):=by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hn] with y hy
      change (∑i:Fin d,A y j i*partialDeriv i φ y)=0
      apply Finset.sum_eq_zero
      intro i _
      rw [image_eq_zero_of_notMem_tsupport (fun h=>hy (tsupport_partial_subset i φ h)),mul_zero]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  have hψc(j:Fin d):HasCompactSupport (ψ j):=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (hψs j)
  have hul:LocallyIntegrable u (volume.restrict O):=hu.memLp.locallyIntegrable (by norm_num)
  have hpl(j:Fin d):LocallyIntegrable (p j) (volume.restrict O):=
    (hu.chosenWeakPartial_mem j).memLp.locallyIntegrable (by norm_num)
  have hpart(j:Fin d):
      (∫x in O,u x*partialDeriv j (ψ j) x)=-(∫x in O,p j x*ψ j x):=
    chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j (ψ j) (hψ j) (hψc j) ((hψs j).trans hs)
  calc
    _ = -(∫x in O,∑j:Fin d,u x*partialDeriv j (ψ j) x) := by
      rw [←integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by simp only [principalSource,ψ,←Finset.mul_sum,mul_neg])
    _ = -(∑j:Fin d,∫x in O,u x*partialDeriv j (ψ j) x) := by
      rw [integral_finsetSum Finset.univ (fun j _=>integrable_mul_partial_test hul (hψ j) (hψc j) j)]
    _ = ∑j:Fin d,∫x in O,p j x*ψ j x := by simp only [hpart,Finset.sum_neg_distrib,neg_neg]
    _ = ∫x in O,∑j:Fin d,p j x*ψ j x := by
      rw [integral_finsetSum Finset.univ (fun j _=>integrable_mul_test (hpl j) (hψ j) (hψc j))]
    _ = ∫x in O,∑i:Fin d,matrixFlux A p i x*partialDeriv i φ x := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [ψ,matrixFlux,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm x j i]
      ring
    _ = _ := weakEquation_weakDivergenceSource hO A hA hu φ hφ hc hs

#print axioms weakDivergenceSource_transposed_test
end Yamabe3.Analysis.UniformElliptic
