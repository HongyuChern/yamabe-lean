import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import Yamabe3.Analysis.UniformElliptic.DivergenceScaling
import Yamabe3.Analysis.UniformElliptic.NativeDivergenceSource

/-!
# Actual local native PDEs supply the rescaled weak divergence equation

A real smooth compact extension near the integration region justifies the
integration by parts. The true coefficient and native Laplacian identities,
not an assumed coordinate weak equation, then provide the rescaled equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

/-- Local smoothness and the actual divergence source give the true weak
identity on every precompact open subregion. The smooth extension is built. -/
theorem weakEquation_of_local_principalSource
    {d : ℕ} {O V : Set (EuclideanSpace ℝ (Fin d))}
    (hO : IsOpen O) (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (heq : ∀ x ∈ V, principalSource a u x = f x) :
    WeakEquation V (matrixFlux a (fun j => partialDeriv j u)) f := by
  obtain ⟨v, hv, _, hvg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hlocal (x) (hx : x ∈ V) : v =ᶠ[𝓝 x] u := hvg x (subset_closure hx)
  have hw := weakEquation_principalSource hV ha hv
  intro φ hφ hφc hφV
  calc
    (∫ x in V, ∑ i, matrixFlux a (fun j => partialDeriv j u) i x * partialDeriv i φ x) =
        ∫ x in V, ∑ i, matrixFlux a (fun j => partialDeriv j v) i x * partialDeriv i φ x := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      have hd (j) : partialDeriv j v x = partialDeriv j u x :=
        congrArg (fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
          A (EuclideanSpace.single j 1)) (hlocal x hx).fderiv_eq
      simp only [matrixFlux, hd]
    _ = ∫ x in V, principalSource a v x * φ x := hw φ hφ hφc hφV
    _ = ∫ x in V, f x * φ x := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      change principalSource a v x * φ x = f x * φ x
      rw [principalSource_eq_of_eventuallyEq a (hlocal x hx), heq x hx]

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- Exact weak equation for the centered rescaling of an actual native
solution. In the Green application u is the locally smooth correction;
F is its already constructed native residual, not a source hypothesis hidden
in the operator definition. -/
theorem weakEquation_rescaled_native_solution
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {O W V : Set E} (hO : IsOpen O) (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u F Vpot : E → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (hP : ∀ y ∈ O, -D.laplacian u y + Vpot y * u y = F y)
    (r b : ℝ) (hrO : MapsTo (fun x : E => r • x) W O) :
    WeakEquation V
      (matrixFlux (fun x => nativeDivergenceMatrix g (r • x))
        (fun j => partialDeriv j (fun x => u (r • x) - b)))
      (fun x =>
        (r ^ 2 * g.pullbackVolumeDensity id (r • x) * F (r • x) -
          r ^ 2 * g.pullbackVolumeDensity id (r • x) * Vpot (r • x) * b) +
        (-r ^ 2 * g.pullbackVolumeDensity id (r • x) * Vpot (r • x)) *
          (u (r • x) - b)) := by
  have hus : ContDiffOn ℝ ∞ (fun x : E => u (r • x) - b) W :=
    (hu.comp (contDiff_id.const_smul r).contDiffOn hrO).sub contDiffOn_const
  apply weakEquation_of_local_principalSource
    (a := fun x => nativeDivergenceMatrix g (r • x)) hW hV hVc hVW
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)) hus
  intro x hx
  have hxO := hrO (hVW (subset_closure hx))
  have hsc := principalSource_scaled_centered (nativeDivergenceMatrix g) u r 1 b x
  simp only [one_mul] at hsc
  change principalSource (fun y => nativeDivergenceMatrix g (r • y))
    (fun y => u (r • y) - b) x = _
  rw [hsc, native_principalSource_eq_negative_density_laplacian g D
    (hu.contDiffAt (hO.mem_nhds hxO))]
  have hLap : -D.laplacian u (r • x) =
      F (r • x) - Vpot (r • x) * u (r • x) := by
    linarith [hP (r • x) hxO]
  calc
    _ = r ^ 2 * g.pullbackVolumeDensity id (r • x) * (-D.laplacian u (r • x)) := by ring
    _ = r ^ 2 * g.pullbackVolumeDensity id (r • x) *
        (F (r • x) - Vpot (r • x) * u (r • x)) := by rw [hLap]
    _ = _ := by ring

#print axioms weakEquation_of_local_principalSource
#print axioms weakEquation_rescaled_native_solution

end Yamabe3.Analysis.UniformElliptic
