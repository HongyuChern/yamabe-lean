import Yamabe3.Analysis.NativeFullZeroSourceH2
import Yamabe3.Analysis.NativeFullCompletionBound
import Yamabe3.Analysis.DelaunayChartPotentialJets
import Yamabe3.Analysis.NativeUnitSphereChartWitness
import Yamabe3.Analysis.BoundaryChartH1Bound

/-! Real zero-entrance remainder of the full-source field: uniform H4
boundary charts, selected before the orbit, phase, and full source.
The finite entrance lift is retained separately, rather than imposing a
false zero boundary condition on the full low-mode solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction Manifold ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem exists_uniform_full_zero_entrance_chart_H4_witness
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (a:E) (ha:‖a‖=1) :
    ∃ (e:OpenPartialHomeomorph E E) (χ:E→ℝ) (U:Set E) (C:ℝ≥0∞),
      a∈e.target ∧ e.symm a∈U ∧ IsOpen U ∧ IsCompact (closure U) ∧
      closure U⊆e.source ∧ e.target⊆halfEndSourceAnnulus ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀x∈e.source,e x∈O ↔ 0<x 0) ∧
      (∀x∈U,χ (e x)=1) ∧ (e.symm a) 0=0 ∧
      ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆e.target ∧ C≠⊤ ∧
      ∀(p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph),
        let z:=fullModelZeroCompletion hκ0 hκ1 p f
        MemWkp 4 2 (chartPullback e (fun y=>χ y*toL2 nativeWeakEuclideanD O z y))
          (U∩{x:E|0<x 0}) ∧
        iteratedWeakSobolevNorm 4 2 (chartPullback e (fun y=>χ y*toL2 nativeWeakEuclideanD O z y))
          (U∩{x:E|0<x 0})≤C*ENNReal.ofReal ‖f‖ := by
  obtain ⟨e,χ,W,U,hae,het,haU,hW,hWc,hWs,hU,hUc,hUW,
    he,hei,hχ,hc,hs,hone,hflat,hface⟩:=exists_unitSphere_chart_data_with_face a ha
  have hzero:∀x∈e.target,x≠0:=by
    intro x hx hz
    have hn:=(het hx).1
    simp only [hz,norm_zero] at hn
    norm_num at hn
  obtain ⟨M,hM,hMj⟩:=exists_uniform_delaunay_chart_potential_jets e he hei hzero hWc hWs 2
  have heW:e '' closure W⊆halfEndSourceAnnulus:=by
    rintro y ⟨x,hx,rfl⟩
    exact het (e.map_source (hWs hx))
  obtain ⟨K,hK,hb⟩:=exists_chart_H4_with_uniform_physical_potential_bound (D:=nativeWeakEuclideanD)
    e he hei χ hχ hc hs hflat hW hWc hWs hone hU hUc hUW
    halfEndSourceAnnulus_isOpen heW hM
  obtain ⟨C₁,hC₁,h1⟩:=QuantitativeChart.exists_chart_first_sobolev_bound (D:=nativeWeakEuclideanD)
    e he hei χ hχ hc hs hflat
  obtain ⟨C₂,hC₂,h2⟩:=exists_uniform_full_zero_completion_bound hκ0 hκ1
  obtain ⟨C₃,hC₃,h3⟩:=exists_uniform_full_zero_source_entrance_H2_bound
  refine ⟨e,χ,U,K*(C₁*ENNReal.ofReal C₂+C₃),hae,haU,hU,hUc,
    hUW.trans (subset_closure.trans hWs),het,he,hei,hflat,
    fun x hx=>hone x (hUW (subset_closure hx)),hface,hχ,hc,hs,by finiteness,?_⟩
  intro p f
  have hQ:ContDiffOn ℝ ∞ (nativeHalfEndPotentialCoefficient p.potential) e.target:=
    (nativeHalfEndPotentialCoefficient_contDiffOn p.potential p.potential_smooth).mono
      (fun x hx=>hzero x hx)
  have hj:∀n≤2,∀x∈W,‖iteratedFDeriv ℝ n
      (fun y=>(RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e y*
        nativeHalfEndPotentialCoefficient p.potential (e y)) x‖≤M:=by
    intro n hn x hx
    rw [fullModelPotential_eq_neg_annular]
    exact hMj p.orbit p.smooth (fun t=>⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩)
      p.ode p.phase n hn x (subset_closure hx)
  let z:=fullModelZeroCompletion hκ0 hκ1 p f
  have hf:=h3 κ p f
  have hr:=hb _ hQ hj z (fullModelZeroPhysicalSource p f)
    (fullModelZeroCompletionRHS hκ0 hκ1 p f) hf.1
    (fullModelZeroCompletion_source hκ0 hκ1 p f)
    (fullModelZeroCompletion_retained_equation hκ0 hκ1 p f)
  have hz:ENNReal.ofReal ‖z‖≤ENNReal.ofReal C₂*ENNReal.ofReal ‖f‖:=by
    simpa only [ENNReal.ofReal_mul hC₂] using ENNReal.ofReal_le_ofReal (h2 p f)
  refine ⟨hr.1,hr.2.trans ?_⟩
  calc
    _ ≤ K*(C₁*(ENNReal.ofReal C₂*ENNReal.ofReal ‖f‖)+C₃*ENNReal.ofReal ‖f‖):=
      mul_le_mul le_rfl (add_le_add ((h1 z).trans
        (mul_le_mul le_rfl hz zero_le zero_le)) hf.2) zero_le zero_le
    _ = _:=by ring

#print axioms exists_uniform_full_zero_entrance_chart_H4_witness
end Yamabe3.Analysis.UniformElliptic
