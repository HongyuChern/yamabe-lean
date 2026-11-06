import GreenMass.InvertedEnd
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Inverted ends on the inherited punctured open manifold

The codomain is the actual `TopologicalSpace.Opens` subtype obtained by
deleting the pole. Its smooth structure is the inherited atlas. The map
coincides with the original coordinate chart composed with inversion on
the entire exterior; its totalization away from that exterior is irrelevant.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GreenMass.PuncturedEnd
open InvertedEnd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

private def liftMap
    (d : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (O : Opens M) [Nonempty O] (hO : d.target ⊆ O) (x : E) : O := by
  classical
  exact if hx : x ∈ d.source then ⟨d x, hO (d.toPartialEquiv.map_source hx)⟩
    else Classical.choice (inferInstance : Nonempty O)

private theorem liftMap_coe
    (d : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (O : Opens M) [Nonempty O] (hO : d.target ⊆ O) (x : E)
    (hx : x ∈ d.source) : (liftMap d O hO x).val = d x := by
  simp only [liftMap, dif_pos hx]

/-- Restriction of a genuine local diffeomorphism to an open codomain
containing its target; no inverse or regularity is assumed for the lift. -/
def restrictCodomain
    (d : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (O : Opens M) [Nonempty O] (hO : d.target ⊆ O) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E O ∞ where
  toFun := liftMap d O hO
  invFun := fun q => d.invFun q.val
  source := d.source
  target := {q : O | q.val ∈ d.target}
  map_source' x hx := by
    change (liftMap d O hO x).val ∈ d.target
    rw [liftMap_coe d O hO x hx]
    exact d.toPartialEquiv.map_source hx
  map_target' q hq := d.toPartialEquiv.map_target hq
  left_inv' x hx := by
    change d.invFun (liftMap d O hO x).val = x
    rw [liftMap_coe d O hO x hx]
    exact d.toPartialEquiv.left_inv hx
  right_inv' q hq := by
    apply Subtype.ext
    change (liftMap d O hO (d.invFun q.val)).val = q.val
    exact (liftMap_coe d O hO _ (d.toPartialEquiv.map_target hq)).trans
      (d.toPartialEquiv.right_inv hq)
  open_source := d.open_source
  open_target := d.open_target.preimage continuous_subtype_val
  contMDiffOn_toFun x hx := by
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff O (liftMap d O hO) x).mp
    apply (d.contMDiffOn_toFun.contMDiffAt (d.open_source.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [d.open_source.mem_nhds hx] with y hy
    exact liftMap_coe d O hO y hy
  contMDiffOn_invFun :=
    d.contMDiffOn_invFun.comp
      (contMDiff_subtype_val (I := 𝓡 3) (U := O) (n := ∞)).contMDiffOn
      (fun _ hq => hq)

theorem restrictCodomain_coe_of_mem
    (d : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (O : Opens M) [Nonempty O] (hO : d.target ⊆ O) (x : E)
    (hx : x ∈ d.source) : (restrictCodomain d O hO x).val = d x :=
  liftMap_coe d O hO x hx

/-- The actual open complement of one point, with the inherited atlas. -/
def puncture [T1Space M] (p : M) : Opens M := ⟨{p}ᶜ, isOpen_compl_singleton⟩

theorem chartEnd_target_subset_puncture [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    (chartEnd e ρ hρ).target ⊆ puncture (e 0) := by
  rw [chartEnd_target e ρ hρ hball]
  exact fun _ h => h.2

/-- A genuine end chart valued in the native punctured open manifold. -/
def puncturedChartEnd [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E (puncture (e 0)) ∞ := by
  let d := chartEnd e ρ hρ
  have ht : d.target ⊆ puncture (e 0) :=
    chartEnd_target_subset_puncture e ρ hρ hball
  letI : Nonempty (puncture (e 0)) := by
    obtain ⟨y, hy⟩ := (exterior_isPathConnected hρ).nonempty
    have hy' : y ∈ d.source := by
      dsimp [d]
      rw [chartEnd_source e ρ hρ hball]
      exact hy
    exact ⟨⟨d y, ht (d.toPartialEquiv.map_source hy')⟩⟩
  exact restrictCodomain d (puncture (e 0)) ht

theorem puncturedChartEnd_source [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    (puncturedChartEnd e ρ hρ hball).source = exterior ρ :=
  chartEnd_source e ρ hρ hball

theorem puncturedChartEnd_target [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    (puncturedChartEnd e ρ hρ hball).target =
      {q : puncture (e 0) | q.val ∈ e '' ball (0 : E) ρ} := by
  ext q
  change q.val ∈ (chartEnd e ρ hρ).target ↔ q.val ∈ e '' ball (0 : E) ρ
  rw [chartEnd_target e ρ hρ hball]
  exact and_iff_left q.property

/-- The lifted actual chart is exactly the original inversion chart on its
whole exterior, not merely a map with the same name or a chosen array. -/
theorem puncturedChartEnd_coe [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source)
    (y : E) (hy : y ∈ exterior ρ) :
    (puncturedChartEnd e ρ hρ hball y).val = e (InversionDifferential.inversion y) := by
  have hy' : y ∈ (chartEnd e ρ hρ).source := by
    rw [chartEnd_source e ρ hρ hball]
    exact hy
  letI : Nonempty (puncture (e 0)) := ⟨puncturedChartEnd e ρ hρ hball y⟩
  exact liftMap_coe (chartEnd e ρ hρ) (puncture (e 0))
    (chartEnd_target_subset_puncture e ρ hρ hball) y hy'

theorem puncturedChartEnd_complement_isCompact [T1Space M] [CompactSpace M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    IsCompact ((puncturedChartEnd e ρ hρ hball).target)ᶜ := by
  exact chartEnd_complement_isCompact e ρ hρ hball

theorem puncturedChartEnd_target_isPathConnected [T1Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    IsPathConnected (puncturedChartEnd e ρ hρ hball).target := by
  have hs : IsPathConnected (puncturedChartEnd e ρ hρ hball).source := by
    rw [puncturedChartEnd_source e ρ hρ hball]
    exact exterior_isPathConnected hρ
  have hi := hs.image' (puncturedChartEnd e ρ hρ hball).contMDiffOn_toFun.continuousOn
  change IsPathConnected ((puncturedChartEnd e ρ hρ hball).toPartialEquiv ''
    (puncturedChartEnd e ρ hρ hball).source) at hi
  rwa [(puncturedChartEnd e ρ hρ hball).toPartialEquiv.image_source_eq_target] at hi

theorem puncturedChartEnd_cofinal [T2Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞) (hzero : (0 : E) ∈ e.source)
    (K : Set (puncture (e 0))) (hK : IsCompact K) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source),
      Disjoint (puncturedChartEnd e ρ hρ hball).target K := by
  obtain ⟨ρ, hρ, hball, hd⟩ := chartEnd_cofinal e hzero K hK
  refine ⟨ρ, hρ, hball, Set.disjoint_left.mpr ?_⟩
  intro q hq hqK
  exact Set.disjoint_left.mp hd hq ⟨q, hqK, rfl⟩

#print axioms restrictCodomain
#print axioms puncturedChartEnd
#print axioms puncturedChartEnd_source
#print axioms puncturedChartEnd_target
#print axioms puncturedChartEnd_coe
#print axioms puncturedChartEnd_complement_isCompact
#print axioms puncturedChartEnd_target_isPathConnected
#print axioms puncturedChartEnd_cofinal

end GreenMass.PuncturedEnd
