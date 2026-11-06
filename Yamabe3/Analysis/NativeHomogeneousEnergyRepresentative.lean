import Yamabe3.Analysis.NativeHomogeneousEnergySpace

/-! A fixed regular representative of each actual homogeneous energy
class is linear on the open homogeneous region. Uniqueness uses native
open-positive volume and continuity, never sphere restriction of AE data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

def nativeHomogeneousEnergyRepresentative
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) (W : nativeHomogeneousEnergySpace g B hB Ω) : M → ℝ :=
  (exists_nativeHomogeneousEnergy_smooth_representative g B hB hΩ W).choose

theorem nativeHomogeneousEnergyRepresentative_spec
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) (W : nativeHomogeneousEnergySpace g B hB Ω) :
    let U := nativeHomogeneousEnergyRepresentative g B hB hΩ W
    ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U Ω ∧
      U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W.val : M → ℝ) ∧
      ∀x∈Ω,-8*g.leviCivitaData.laplacian U x+
        (g.leviCivitaData.scalarCurvature x-30*B x^4)*U x=0 :=
  (exists_nativeHomogeneousEnergy_smooth_representative g B hB hΩ W).choose_spec

theorem nativeHomogeneousEnergyRepresentative_add
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) (W Z : nativeHomogeneousEnergySpace g B hB Ω) :
    EqOn (nativeHomogeneousEnergyRepresentative g B hB hΩ (W+Z))
      (fun x => nativeHomogeneousEnergyRepresentative g B hB hΩ W x+
        nativeHomogeneousEnergyRepresentative g B hB hΩ Z x) Ω := by
  letI : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have hW := nativeHomogeneousEnergyRepresentative_spec g B hB hΩ W
  have hZ := nativeHomogeneousEnergyRepresentative_spec g B hB hΩ Z
  have hS := nativeHomogeneousEnergyRepresentative_spec g B hB hΩ (W+Z)
  have hmap : (toL2 g.leviCivitaData univ (W+Z).val : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (fun x => toL2 g.leviCivitaData univ W.val x+toL2 g.leviCivitaData univ Z.val x) := by
    rw [show (W+Z).val=W.val+Z.val from rfl,map_add]
    exact ae_restrict_of_ae (Lp.coeFn_add _ _)
  have ha := hS.2.1.trans (hmap.trans (hW.2.1.symm.add hZ.2.1.symm))
  exact Measure.eqOn_open_of_ae_eq ha hΩ hS.1.continuousOn (hW.1.continuousOn.add hZ.1.continuousOn)

theorem nativeHomogeneousEnergyRepresentative_smul
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) (c : ℝ) (W : nativeHomogeneousEnergySpace g B hB Ω) :
    EqOn (nativeHomogeneousEnergyRepresentative g B hB hΩ (c • W))
      (fun x => c*nativeHomogeneousEnergyRepresentative g B hB hΩ W x) Ω := by
  letI : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have hW := nativeHomogeneousEnergyRepresentative_spec g B hB hΩ W
  have hS := nativeHomogeneousEnergyRepresentative_spec g B hB hΩ (c • W)
  have hmap : (toL2 g.leviCivitaData univ (c • W).val : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (fun x => c*toL2 g.leviCivitaData univ W.val x) := by
    rw [show (c • W).val=c • W.val from rfl,map_smul]
    exact ae_restrict_of_ae (Lp.coeFn_smul c _)
  have ha : nativeHomogeneousEnergyRepresentative g B hB hΩ (c • W) =ᵐ[g.volumeMeasure.restrict Ω]
      (fun x => c*nativeHomogeneousEnergyRepresentative g B hB hΩ W x) := by
    refine hS.2.1.trans (hmap.trans ?_)
    filter_upwards [hW.2.1] with x hx
    rw [hx]
  exact Measure.eqOn_open_of_ae_eq ha hΩ hS.1.continuousOn (continuousOn_const.mul hW.1.continuousOn)

def nativeHomogeneousEnergyRepresentativeLinear
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) : nativeHomogeneousEnergySpace g B hB Ω →ₗ[ℝ] (M → ℝ) where
  toFun W := Ω.indicator (nativeHomogeneousEnergyRepresentative g B hB hΩ W)
  map_add' W Z := by
    funext x
    by_cases hx : x∈Ω
    · simp only [indicator_of_mem hx,Pi.add_apply]
      exact nativeHomogeneousEnergyRepresentative_add g B hB hΩ W Z hx
    · simp only [indicator_of_notMem hx,Pi.add_apply,zero_add]
  map_smul' c W := by
    funext x
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul]
    by_cases hx : x∈Ω
    · simp only [indicator_of_mem hx]
      exact nativeHomogeneousEnergyRepresentative_smul g B hB hΩ c W hx
    · simp only [indicator_of_notMem hx,mul_zero]

#print axioms nativeHomogeneousEnergyRepresentative_spec
#print axioms nativeHomogeneousEnergyRepresentative_add
#print axioms nativeHomogeneousEnergyRepresentative_smul
#print axioms nativeHomogeneousEnergyRepresentativeLinear
end Yamabe3.Analysis.SpherePolar
