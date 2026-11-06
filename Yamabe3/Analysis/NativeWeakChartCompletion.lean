import Yamabe3.Analysis.NativeWeakChartTransport
import Yamabe3.Analysis.NativeWeakH01EnergyNorm
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses

/-!
# The original weak function in the actual manifold completion

The original pinned MemH01 adapter and its manifold realization are
checked in one compilation unit. Their public names and proof blocks
are retained verbatim. NativeWeakH01Completion is a compatibility import.
The separately verified lightweight modules provide the actual weak
energy and coordinate-transport constructions; no trace is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak
local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The original weak H1-zero definition produces a native completed
element whose actual L2 representative is the original zero extension. -/
theorem exists_nativeEuclideanH01_of_memH01
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemH01 u O) :
    ∃ z : H1Zero nativeWeakEuclideanD O,
      (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[volume] O.indicator u := by
  rcases hu with ⟨_, w, ψ, hψ, hc, hs, hv, hd⟩
  exact exists_nativeEuclideanH01_of_approximation hO u w.weakGrad
    w.memLp w.weakGrad_component_memLp ψ hψ hc hs hv hd

/-- Every supplied genuine weak gradient of this same function gives the
same native energy pairing. Weak derivative uniqueness, rather than a new
choice of gradient, connects the original PDE producer to the completion. -/
theorem nativeEuclidean_memH01_gradient_pairing
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemH01 u O)
    (du : Fin 3 → E → ℝ) (hdu : ∀ i, MemLp (du i) 2 (volume.restrict O))
    (hwdu : ∀ i, HasWeakPartialDeriv i (du i) u O)
    (z : H1Zero nativeWeakEuclideanD O)
    (hz : (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[volume] O.indicator u)
    (η : EnergyTest nativeWeakEuclideanD O) :
    gradientEnergy nativeWeakEuclideanD O z (η : H1Zero nativeWeakEuclideanD O) =
      ∑ i : Fin 3, ∫ x in O, du i x *
        fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) := by
  rcases hu with ⟨_, w, ψ, hψ, hc, hs, hv, hd⟩
  let φ (n : ℕ) : EnergyTest nativeWeakEuclideanD O :=
    ⟨ψ n, (hψ n).contMDiff, hc n, hs n⟩
  rw [nativeEuclidean_gradient_pairing_of_weak_approximation
    hO φ u w.weakGrad w.memLp w.weakGrad_component_memLp hv hd z hz η]
  apply Finset.sum_congr rfl
  intro i _
  have hsame := HasWeakPartialDeriv.ae_eq hO (w.isWeakGrad i) (hwdu i)
    ((w.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hdu i).locallyIntegrable (by norm_num))
  apply integral_congr_ae
  filter_upwards [hsame] with x hx
  rw [hx]

/-- The native norm is exactly the original value and weak-gradient
energy. In particular, quantitative bounds on the original physical
function transfer with constant one before changing coordinates. -/
theorem nativeEuclidean_memH01_norm_sq
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemH01 u O)
    (du : Fin 3 → E → ℝ) (hdu : ∀ i, MemLp (du i) 2 (volume.restrict O))
    (hwdu : ∀ i, HasWeakPartialDeriv i (du i) u O)
    (z : H1Zero nativeWeakEuclideanD O)
    (hz : (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[volume] O.indicator u) :
    ‖z‖ ^ 2 = (∫ x in O, u x ^ 2) + ∑ i : Fin 3, ∫ x in O, du i x ^ 2 := by
  rcases hu with ⟨_, w, ψ, hψ, hc, hs, hv, hd⟩
  let φ (n : ℕ) : EnergyTest nativeWeakEuclideanD O :=
    ⟨ψ n, (hψ n).contMDiff, hc n, hs n⟩
  rw [nativeEuclidean_norm_sq_of_weak_approximation
    hO φ u w.weakGrad w.memLp w.weakGrad_component_memLp hv hd z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hsame := HasWeakPartialDeriv.ae_eq hO (w.isWeakGrad i) (hwdu i)
    ((w.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hdu i).locallyIntegrable (by norm_num))
  apply integral_congr_ae
  filter_upwards [hsame] with x hx
  rw [hx]

/-- The actual weak predicate supplies the native representative, and its
native gradient agrees with any original L2 weak-gradient witness. -/
theorem exists_nativeEuclideanH01_of_memH01_with_gradient
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemH01 u O)
    (du : Fin 3 → E → ℝ) (hdu : ∀ i, MemLp (du i) 2 (volume.restrict O))
    (hwdu : ∀ i, HasWeakPartialDeriv i (du i) u O) :
    ∃ z : H1Zero nativeWeakEuclideanD O,
      (toL2 nativeWeakEuclideanD O z : E → ℝ) =ᵐ[volume] O.indicator u ∧
      ∀ η : EnergyTest nativeWeakEuclideanD O,
        gradientEnergy nativeWeakEuclideanD O z (η : H1Zero nativeWeakEuclideanD O) =
          ∑ i : Fin 3, ∫ x in O, du i x *
            fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single i 1) := by
  obtain ⟨z, hz⟩ := exists_nativeEuclideanH01_of_memH01 hO hu
  exact ⟨z, hz, nativeEuclidean_memH01_gradient_pairing hO hu du hdu hwdu z hz⟩

#print axioms exists_nativeEuclideanH01_of_memH01
#print axioms nativeEuclidean_memH01_gradient_pairing
#print axioms nativeEuclidean_memH01_norm_sq
#print axioms exists_nativeEuclideanH01_of_memH01_with_gradient

end Yamabe3.Analysis.SpherePolar


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory UniformSpace PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak

universe u
variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The transported element represents exactly the original weak function
on the coordinate domain, extended by zero. The input never includes a
trace or an asserted Sobolev realization. -/
theorem exists_nativeWeakChartH01_of_memH01
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    {f : E → ℝ} (hf : Measurable f) (hf1 : MemH01 f O) :
    ∃ z : H1Zero g.leviCivitaData (e '' O),
      (toL2 g.leviCivitaData (e '' O) z : M → ℝ) =ᵐ[g.volumeMeasure]
        coordinateExtension e (O.indicator f) := by
  obtain ⟨w, hw⟩ := exists_nativeEuclideanH01_of_memH01 hO hf1
  refine ⟨nativeWeakChartH1CLM g e he hei hK hKs hOK w, ?_⟩
  rw [toL2_nativeWeakChartH1CLM]
  have hwm : MemLp (toL2 euclideanD O w : E → ℝ) 2 volume := by
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.memLp (toL2 euclideanD O w)
  have hfm : MemLp (O.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hO.measurableSet).mpr hf1.1.1
  have hc := nativeCompactChartFunction_congr_ae g e he hei hK hKs
    (Lp.stronglyMeasurable (toL2 euclideanD O w)).measurable
    (hf.indicator hO.measurableSet) hwm hfm hw
  have hind : K.indicator (O.indicator f) = O.indicator f := by
    funext x
    by_cases hx : x ∈ O
    · simp [hx, hOK hx]
    · by_cases hKx : x ∈ K <;> simp [hx, hKx]
  have hc' : nativeCompactChartFunction e K (toL2 euclideanD O w) =ᵐ[g.volumeMeasure]
      coordinateExtension e (O.indicator f) := by
    simpa only [nativeCompactChartFunction, hind] using hc
  exact (nativeCompactChartL2Linear_ae g e he hei hK hKs (toL2 euclideanD O w)).trans hc'

#print axioms exists_nativeWeakChartH01_of_memH01

end Yamabe3.Analysis.SpherePolar
