import Yamabe3.Analysis.NativeManifoldC1Green
import Yamabe3.Analysis.NativeC1ChartEnergyTrace
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakReplacement

/-! A compact C1 chart representative has its genuine manifold C1
regularity. Any actual H1 completion with that same native volume class
has the classical gradient pairing against smooth energy tests. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet NativeC1Green
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem contMDiff_coordinateExtension_C1
    (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ) (hs:tsupport φ⊆e.source) :
    ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 (coordinateExtension e φ) := by
  apply contMDiff_of_tsupport
  intro y hy
  obtain ⟨x,hx,rfl⟩:=tsupport_coordinateExtension_subset_image e hc hs hy
  have hyt:=e.map_source (hs hx)
  apply ContMDiffAt.congr_of_eventuallyEq _ (coordinateExtension_eventuallyEq e φ hyt)
  exact hφ.contMDiff.contMDiffAt.comp (e x)
    ((hei.contMDiffAt (e.open_target.mem_nhds hyt)).of_le (by simp))

variable [PreconnectedSpace M]

theorem native_H1_C1_representative_gradientEnergy
    (g:RiemannianMetric 3 M) {Ω:Set M} (w:H1Zero g.leviCivitaData Ω)
    {U:M→ℝ} (hU:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) 1 U) (hc:HasCompactSupport U)
    (hrep:(toL2 g.leviCivitaData Ω w:M→ℝ)=ᵐ[g.volumeMeasure] U)
    (φ:EnergyTest g.leviCivitaData Ω) :
    gradientEnergy g.leviCivitaData Ω w (φ:H1Zero g.leviCivitaData Ω)=
      ∫x,g.inner x (g.leviCivitaData.gradient U x) (g.leviCivitaData.gradient φ x) ∂g.volumeMeasure := by
  rw [gradientEnergy_eq_neg_inner_laplacianLp,inner_laplacianLp_eq_integral]
  have he:(∫x,toL2 g.leviCivitaData Ω w x*g.leviCivitaData.laplacian φ x ∂g.volumeMeasure)=
      ∫x,U x*g.leviCivitaData.laplacian φ x ∂g.volumeMeasure:=by
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
  rw [he,integral_mul_laplacian_of_compact_C1_test g.leviCivitaData hU φ.smooth hc,neg_neg]

theorem native_H1_C1_chart_representative_gradientEnergy
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U:E→ℝ} (hU:ContDiff ℝ 1 U) (hc:HasCompactSupport U) (hs:tsupport U⊆e.source)
    {Ω:Set M} (w:H1Zero g.leviCivitaData Ω)
    (hrep:(toL2 g.leviCivitaData Ω w:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension e U)
    (φ:EnergyTest g.leviCivitaData Ω) :
    gradientEnergy g.leviCivitaData Ω w (φ:H1Zero g.leviCivitaData Ω)=
      ∫x,g.inner x (g.leviCivitaData.gradient (coordinateExtension e U) x)
        (g.leviCivitaData.gradient φ x) ∂g.volumeMeasure :=
  native_H1_C1_representative_gradientEnergy g w (contMDiff_coordinateExtension_C1 e hei hU hc hs)
    (hasCompactSupport_coordinateExtension e hc hs) hrep φ

#print axioms contMDiff_coordinateExtension_C1
#print axioms native_H1_C1_representative_gradientEnergy
#print axioms native_H1_C1_chart_representative_gradientEnergy
end Yamabe3.Analysis
