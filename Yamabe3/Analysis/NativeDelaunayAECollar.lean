import Yamabe3.Analysis.NativeDelaunayUniformCollar
import Yamabe3.Analysis.DelaunayPhaseData
import Yamabe3.Analysis.NativeDelaunayEntranceH4
import Yamabe3.Analysis.BoundaryLinearExtensionAE
import Yamabe3.Analysis.UniformFamilyCollar

/-! One physical H4 collar neighborhood and one bound, before the actual
Delaunay orbit, its phase and the original source. The extension agrees
with the one canonical completion, hence with the original positive field.
This does not yet assert the all-scale weighted graph estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0 : E) 1 \ {(0 : E)}

theorem exists_uniform_delaunay_physical_local_collar_ae_operator
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (a : E) (ha : ‖a‖ = 1) :
    ∃ (N : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N ⊆ halfEndSourceAnnulus ∧ C ≠ ⊤ ∧
      (∀ u v : E → ℝ, u =ᵐ[volume] v → L u =ᵐ[volume.restrict N] L v) ∧
      ∀ p f, MemWkp 4 2 (L (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) N ∧
        iteratedWeakSobolevNorm 4 2 (L (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) N ≤ C*ENNReal.ofReal ‖f.1‖ ∧
        EqOn (L (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) (N ∩ O) := by
  obtain ⟨e,χ,U,A,hae,haU,hU,hUc,hUs,het,he,hei,hflat,hone,hA,hreg⟩ :=
    exists_uniform_delaunay_entrance_chart_H4_bound hκ0 hκ1 a ha
  obtain ⟨N,T,B,haN,hN,hNc,hNt,hB,hb⟩ :=
    exists_chart_physical_linear_extension e he hei hflat χ hU hone a hae haU
  refine ⟨N,T,B*A,haN,hN,hNc,hNt.trans het,by finiteness,?_,?_⟩
  · intro u v huv
    exact linear_chart_extension_congr_ae e he hei χ hU hN T B
      (fun w hw => ⟨(hb w hw).1,(hb w hw).2.1⟩) huv
  intro p f
  have hf := hreg p.orbit p.smooth (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩)
    p.ode p.phase p.potential (fun _ => rfl) p.kernel_bound p.potential_nonneg p.potential_smooth f
  have hh := hb _ hf.1
  refine ⟨hh.1,hh.2.1.trans ?_,hh.2.2⟩
  simpa only [mul_assoc,Poincare.Analysis.Sobolev.BoundaryTangential.halfSpace] using
    mul_le_mul (a := B) le_rfl hf.2 zero_le zero_le


theorem exists_uniform_delaunay_compact_H4_collar_ae_operator
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ (U : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      IsOpen U ∧ Metric.sphere (0:E) 1 ⊆ U ∧ C ≠ ⊤ ∧
      (∀ u v : E → ℝ, u =ᵐ[volume] v → L u =ᵐ[volume] L v) ∧
      ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
        let u : E → ℝ := toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)
        HasCompactSupport (L u) ∧ MemWkp 4 2 (L u) univ ∧
        iteratedWeakSobolevNorm 4 2 (L u) univ ≤ C*ENNReal.ofReal ‖f.1‖ ∧
        EqOn (L u) u (U ∩ O) := by
  classical
  let K : Set E := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hnorm (a : K) : ‖(a:E)‖ = 1 := by
    simpa only [K,Metric.mem_sphere,dist_zero_right] using a.2
  choose N L C haN hN hNc hNs hC hae hl using fun a : K =>
    exists_uniform_delaunay_physical_local_collar_ae_operator hκ0 hκ1 a (hnorm a)
  obtain ⟨s,U,ρ,hU,hKU,hρ,hρc,hρs,hpart⟩ :=
    exists_finite_neighborhood_partition hK N hN haN
  obtain ⟨D,hD,hb⟩ := exists_finitePhysicalPatch_bound 4 (fun i : s => N i.1)
    (fun i => hN i.1) ρ hρ hρc hρs
  let T : (E → ℝ) →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun u => finitePhysicalPatch ρ (fun i : s => L i.1 u)
      map_add' := by
        intro u v
        funext x
        simp only [finitePhysicalPatch,map_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        funext x
        simp only [finitePhysicalPatch,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
        simp only [mul_left_comm,Finset.mul_sum] }
  refine ⟨U,T,∑ i : s, D i*C i.1,hU,hKU,
    ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top (hD i) (hC i.1)),?_,?_⟩
  · intro u v huv
    have hi (i : s) : ∀ᵐ x ∂volume, x ∈ N i.1 → L i.1 u x = L i.1 v x :=
      (ae_restrict_iff' (hN i.1).measurableSet).mp (hae i.1 u v huv)
    filter_upwards [eventually_all.mpr hi] with x hx
    change (∑ i : s, ρ i x * L i.1 u x) = ∑ i : s, ρ i x * L i.1 v x
    apply Finset.sum_congr rfl
    intro i _
    by_cases hin : x ∈ N i.1
    · rw [hx i hin]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hin (hρs i ht)),zero_mul,zero_mul]
  intro p f
  let u : E → ℝ := toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)
  have hh := hb (fun i : s => L i.1 u) (fun i => (hl i.1 p f).1)
  refine ⟨finitePhysicalPatch_compact ρ _ hρc,hh.1,hh.2.trans ?_,?_⟩
  · calc
      _ ≤ ∑ i : s, D i*(C i.1*ENNReal.ofReal ‖f.1‖) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul le_rfl (hl i.1 p f).2.1 zero_le zero_le)
      _ = _ := by simp only [Finset.sum_mul,mul_assoc]
  · exact finitePhysicalPatch_eq_on ρ (fun i : s => L i.1 u) u hρs hpart
      (fun i => (hl i.1 p f).2.2)

#print axioms exists_uniform_delaunay_physical_local_collar_ae_operator
#print axioms exists_uniform_delaunay_compact_H4_collar_ae_operator
end Yamabe3.Analysis.UniformElliptic
