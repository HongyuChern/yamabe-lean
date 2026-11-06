import Yamabe3.Analysis.TransmissionPhysicalExtension
import Yamabe3.Analysis.NativeUnitSphereChart
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Boundary.H3

/-! The actual unit-sphere chart gives a physical one-sided H4 extension.
All neighborhoods and bounds are fixed before the field and source pieces. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
open PoincareMT.LeviCivitaData.Dirichlet.Boundary
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_unitSphere_transmission_neighborhood {D : Set E}
    (g : RiemannianMetric 3 E)
    (hD : IsOpen D) (a : E) (ha : ‖a‖=1) (haD : a∈D) :
    ∃ (N W : Set E) (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞),
      (a:E)∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆D ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W⊆D ∧ C≠⊤ ∧
      ∀ u fpos fneg : E → ℝ,
        MemWkpLocally 2 u D → MemWkp 2 2 fpos W → MemWkp 2 2 fneg W →
        (weakDivergenceSource W (nativeDivergenceMatrix g) u =ᵐ[volume.restrict W]
          physicalSplitSource (Metric.ball (0:E) 1) fpos fneg) →
        MemWkp 4 2 (L u) N ∧
        iteratedWeakSobolevNorm 4 2 (L u) N≤C*
          (iteratedWeakSobolevNorm 2 2 u W+
            (iteratedWeakSobolevNorm 2 2 fpos W+iteratedWeakSobolevNorm 2 2 fneg W)) ∧
        EqOn (L u) u (N∩Metric.ball (0:E) 1) := by
  obtain ⟨e,hae,het,he,hei,hpuncture,-⟩ := exists_unitSphere_flattening_chart a ha
  have hflat : ∀ x∈e.source,e x∈Metric.ball (0:E) 1 ↔ 0<x 0 := by
    intro x hx
    have hxW := het (e.map_source hx)
    have hx0 : e x≠0 := by
      intro heq
      change (3/4:ℝ)<‖e x‖ ∧ ‖e x‖<3/2 at hxW
      norm_num [heq] at hxW
    simpa only [Set.mem_sdiff,mem_singleton_iff,hx0,not_false_eq_true,and_true] using hpuncture x hx
  obtain ⟨W,hW,haW,hWD,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=(a:E))) hD (singleton_subset_iff.mpr haD)
  let Q := e.source∩e ⁻¹' W
  have hQ : IsOpen Q := e.continuousOn.isOpen_inter_preimage e.open_source hW
  have haQ : e.symm a∈Q := by
    refine ⟨e.map_target hae,?_⟩
    change e (e.symm a)∈W
    rw [e.right_inv hae]
    exact haW (mem_singleton _)
  obtain ⟨U,hU,haU,hUQ,hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=e.symm a)) hQ (singleton_subset_iff.mpr haQ)
  have hUs : closure U⊆e.source := fun x hx => (hUQ hx).1
  have heW : e '' closure U⊆W := by
    rintro y ⟨x,hx,rfl⟩
    exact (hUQ hx).2
  obtain ⟨O,hO,haO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=e.symm a)) hU haU
  obtain ⟨V,hV,haV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=e.symm a)) hO haO
  obtain ⟨B,hBT,-⟩ := exists_elliptic_form_on_compact (g:=g) e he hei hUc hUs
  obtain ⟨A,hA,hreg⟩ := exists_native_chart_transmission_H4_estimate g e he hei
    hO hOc hV hVc hVO hU hUc hOU hUs hW hWc heW hWD hflat B
    (fun x hx => hBT (subset_closure hx))
  have hVs : V⊆e.source := subset_closure.trans (hVO.trans (subset_closure.trans (hOU.trans (subset_closure.trans hUs))))
  obtain ⟨N,L,K,haN,hN,hNc,hNt,hK,hext⟩ := exists_transmission_chart_physical_extension
    e he hei hflat hV hVs a hae (haV (mem_singleton _))
  obtain ⟨N',hN',haN',hN'D,hN'c⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x:=(a:E))) (hN.inter hD) (singleton_subset_iff.mpr ⟨haN,haD⟩)
  have hsub : N'⊆N := subset_closure.trans (fun x hx => (hN'D hx).1)
  refine ⟨N',W,L,K*A,haN' (mem_singleton _),hN',hN'c,
    (fun x hx => (hN'D hx).2),hW,hWc,hWD,by finiteness,?_⟩
  intro u fpos fneg hu hfpos hfneg hsource
  have hr := hreg u fpos fneg hu hfpos hfneg hsource
  have hh := hext u hr.1
  refine ⟨hh.1.mono_set (by norm_num) hN' hsub,?_,hh.2.2.mono (inter_subset_inter_left (Metric.ball (0:E) 1) hsub)⟩
  exact (wkpNorm_mono_set (by norm_num) hN' hsub hh.1).trans (hh.2.1.trans
    (by simpa only [mul_assoc] using mul_le_mul (le_refl K) hr.2 zero_le zero_le))

#print axioms exists_unitSphere_transmission_neighborhood
end Yamabe3.Analysis.UniformElliptic
