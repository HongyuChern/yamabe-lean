import Yamabe3.Analysis.WeakDivergenceTransposedTest
import Yamabe3.Analysis.NativeCompactConformalEquation
import Yamabe3.Analysis.WeakDivergenceOperatorContinuity
import Yamabe3.Analysis.OffZeroCompactL2

/-! Local actual H2 functions satisfy the full native conformal
transposed equation, using the same chosen weak second derivatives.
This supplies local tests without pointwise or C-infinity regularity of u. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Manifold Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates PoincareMT.LeviCivitaData.Dirichlet

def nativeWeakConformalDensity (O:Set E) (g:RiemannianMetric 3 E) (u:E→ℝ) (x:E):ℝ:=
  8*weakDivergenceSource O (nativeDivergenceMatrix g) u x+
    g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*u x

theorem nativeWeakConformalDensity_memLp {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O))
    (g:RiemannianMetric 3 E) {u:E→ℝ} (hu:MemWkp 2 2 u O) :
    MemLp (nativeWeakConformalDensity O g u) 2 (volume.restrict O) := by
  obtain ⟨C,hC,hD⟩:=exists_weakDivergenceSource_bound hO hOc (nativeDivergenceMatrix g)
    (contDiff_nativeDivergenceMatrix g)
  have hcoef:Continuous (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x):=
    (native_density_smooth_positive g).1.continuous.mul g.leviCivitaData.contMDiff_scalarCurvature.continuous
  have hm:MemLp (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x) ⊤ (volume.restrict O):=
    (continuousOn_compact_memLp_top hOc hcoef.continuousOn).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  apply (((hD u hu).1.memLp.const_mul 8).add (hu.memLp.mul' hm)).ae_eq
  exact Eventually.of_forall (fun x=>by dsimp only [Pi.add_apply];unfold nativeWeakConformalDensity;ring)

theorem nativeH2_conformal_transposed_test {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O))
    (g:RiemannianMetric 3 E) {u:E→ℝ} (hu:MemWkp 2 2 u O)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (hs:tsupport φ⊆O) :
    (∫x in O,u x*nativeConformalDensityTest g φ x)=
      ∫x in O,nativeWeakConformalDensity O g u x*φ x := by
  have hsymm (x:E) (i j:Fin 3):nativeDivergenceMatrix g x i j=nativeDivergenceMatrix g x j i:=by
    exact divergenceCoefficients_symm (g:=g) (OpenPartialHomeomorph.refl E)
      contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn (mem_univ x) i j
  have hp:principalSource (nativeDivergenceMatrix g) φ=fun x=>-g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian φ x:=by
    funext x
    exact native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData
      (hφ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have ht:=weakDivergenceSource_transposed_test hO (nativeDivergenceMatrix g)
    (contDiff_nativeDivergenceMatrix g) hsymm hu φ hφ hc hs
  have hpc:Continuous (fun x=>-g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian φ x):=
    (native_density_smooth_positive g).1.continuous.neg.mul
      (g.leviCivitaData.contMDiff_laplacian hφ.contMDiff).continuous
  have hps:HasCompactSupport (fun x=>-g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian φ x):=
    (g.leviCivitaData.hasCompactSupport_laplacian hc).mul_left
  have hpm:MemLp (principalSource (nativeDivergenceMatrix g) φ) 2 (volume.restrict O):=by
    rw [hp]
    exact (hpc.memLp_of_hasCompactSupport hps).restrict O
  have hi:Integrable (fun x=>u x*principalSource (nativeDivergenceMatrix g) φ x) (volume.restrict O):=
    hu.memLp.integrable_mul hpm
  have hRc:ContDiff ℝ ∞ (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x):=
    ((native_density_smooth_positive g).1.mul g.leviCivitaData.contMDiff_scalarCurvature.contDiff).mul hφ
  have hRcs:HasCompactSupport (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x):=hc.mul_left
  have hRi:Integrable (fun x=>u x*(g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x))
      (volume.restrict O):=
    hu.memLp.integrable_mul ((hRc.continuous.memLp_of_hasCompactSupport hRcs).restrict O (p:=2))
  obtain ⟨C,hC,hD⟩:=exists_weakDivergenceSource_bound hO hOc (nativeDivergenceMatrix g)
    (contDiff_nativeDivergenceMatrix g)
  have hDi:Integrable (fun x=>weakDivergenceSource O (nativeDivergenceMatrix g) u x*φ x) (volume.restrict O):=
    (hD u hu).1.memLp.integrable_mul ((hφ.continuous.memLp_of_hasCompactSupport hc (p:=2)).restrict O)
  calc
    _ = ∫x in O,8*(u x*principalSource (nativeDivergenceMatrix g) φ x)+
        u x*(g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by rw [hp];unfold nativeConformalDensityTest;ring)
    _ = 8*(∫x in O,u x*principalSource (nativeDivergenceMatrix g) φ x)+
        ∫x in O,u x*(g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x) := by
      rw [integral_add (hi.const_mul 8) hRi,integral_const_mul]
    _ = 8*(∫x in O,weakDivergenceSource O (nativeDivergenceMatrix g) u x*φ x)+
        ∫x in O,u x*(g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x) := by rw [ht]
    _ = ∫x in O,8*(weakDivergenceSource O (nativeDivergenceMatrix g) u x*φ x)+
        u x*(g.pullbackVolumeDensity id x*g.leviCivitaData.scalarCurvature x*φ x) := by
      rw [integral_add (hDi.const_mul 8) hRi,integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by unfold nativeWeakConformalDensity;ring)

#print axioms nativeWeakConformalDensity_memLp
#print axioms nativeH2_conformal_transposed_test
end Yamabe3.Analysis.SpherePolar
