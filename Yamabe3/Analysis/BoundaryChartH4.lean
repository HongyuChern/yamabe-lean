/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Heat/Dirichlet/Boundary/H2.lean

Uses the retained chart-localization interface for the boundary H4 theorem.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.BoundaryLocalH4
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Boundary.H3

/-!
# Retained weak solution at a genuine flattening chart
The actual energy solution and actual volume density produce the coordinate
weak equation. Local H2 regularity of its density-weighted source gives H4
of the same localized representative. This is a chart interface: its source
H2 condition is explicit and is not claimed to be discharged for the half-end.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev
open PoincareMT PoincareMT.LeviCivitaData PoincareMT.LeviCivitaData.Dirichlet
open PoincareMT.LeviCivitaData.Dirichlet.Boundary
variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- H4 for the same energy solution, in the actual flattening chart. The
source is the actual density-weighted pullback, not an arbitrary replacement. -/
theorem chart_H4_of_retained_weakSolution
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWs : closure W ⊆ e.source) (hone : ∀ z ∈ W, χ (e z) = 1)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    (u : H1Zero D Ω) (f : Lp ℝ 2 g.volumeMeasure)
    (hsol : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ)
    (hf2 : Euclidean.MemWkp 2 2 (fun z => g.pullbackVolumeDensity e z * f (e z))
      (W ∩ {z : E | 0 < z 0})) :
    Euclidean.MemWkp 4 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
      (V ∩ {z : E | 0 < z 0}) := by
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hWH := hW.inter hH
  obtain ⟨B, hBA, -⟩ := exists_elliptic_form_on_compact (g := g) e he hei hWc hWs
  obtain ⟨hu0, p, hp, hw, -, -, heq⟩ := weakSolution_localized_divergence
    e he hei χ hχ hc hs hflat hW hWc hWs hone u f hsol
  have hchosen (j : Fin n) : Euclidean.chosenWeakPartial' 2 j F H =ᵐ[volume.restrict H] p j :=
    Weak.HasWeakPartialDeriv.ae_eq hH
      (Euclidean.chosenWeakPartial'_isWeakPartial_of_mem hu0.1 j) (hw j)
      ((Euclidean.chosenWeakPartial'_memLp_of_mem hu0.1 j).locallyIntegrable (by norm_num))
      ((hp j).locallyIntegrable (by norm_num))
  apply flat_local_H4_of_weakEquation B hW hWc hV hVc hVW hu0 hf2
  intro φ hφ hφc hφs
  change (∫ z in W ∩ H, ∑ i : Fin n, ∑ j : Fin n,
    B.a z i j * Euclidean.chosenWeakPartial' 2 j F H z *
      fderiv ℝ φ z (EuclideanSpace.single i 1)) = _
  refine Eq.trans ?_ (heq φ hφ hφc hφs)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hWH.measurableSet,
    (eventually_all.mpr hchosen).filter_mono
      (ae_mono (Measure.restrict_mono_set volume inter_subset_right))] with z hz hpz
  change (∑ i : Fin n, ∑ j : Fin n, B.a z i j *
    Euclidean.chosenWeakPartial' 2 j F H z * fderiv ℝ φ z (EuclideanSpace.single i 1)) = _
  simp only [hBA (subset_closure hz.1), hpz]

#print axioms chart_H4_of_retained_weakSolution
end Yamabe3.Analysis.UniformElliptic
