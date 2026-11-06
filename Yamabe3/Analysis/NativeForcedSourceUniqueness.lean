import Yamabe3.Analysis.NativeForcedEnergySpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Source equality is proved by genuine native compact smooth tests.
It is a volume-a.e. assertion and supplies no restriction to a sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeL2_source_test_pairing (g:RiemannianMetric 3 M) (F:Lp ℝ 2 g.volumeMeasure)
    (φ:EnergyTest g.leviCivitaData univ):
    inner ℝ F (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))=
      ∫y,F y*φ y ∂g.volumeMeasure:=by
  rw [L2.inner_def,toL2_coe]
  apply integral_congr_ae
  filter_upwards [φ.memLp.coeFn_toLp] with y hy
  simp only [Real.inner_apply]
  change F y*(φ.memLp.toLp φ) y=_
  rw [hy]

theorem nativeForcedEnergy_congr_source
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω:Set M} (hΩ:MeasurableSet Ω) (W:H1Zero g.leviCivitaData univ)
    (F G:Lp ℝ 2 g.volumeMeasure)
    (hFG:(F:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω](G:M→ℝ))
    (hW:(W,F)∈nativeForcedEnergySpace g B hB Ω):
    (W,G)∈nativeForcedEnergySpace g B hB Ω:=by
  intro φ hs
  rw [hW φ hs,nativeL2_source_test_pairing,nativeL2_source_test_pairing]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ).mp hFG] with y hy
  by_cases h:y∈Ω
  · rw [hy h]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht=>h (hs ht)),mul_zero,mul_zero]

theorem nativeForcedEnergy_source_unique
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω:Set M} (hΩ:IsOpen Ω) (W:H1Zero g.leviCivitaData univ)
    (F G:Lp ℝ 2 g.volumeMeasure)
    (hF:(W,F)∈nativeForcedEnergySpace g B hB Ω)
    (hG:(W,G)∈nativeForcedEnergySpace g B hB Ω):
    (F:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω](G:M→ℝ):=by
  have hloc:LocallyIntegrableOn (fun y=>F y-G y) Ω g.volumeMeasure:=
    (((Lp.memLp F).sub (Lp.memLp G)).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
  have hz:=hΩ.ae_eq_zero_of_integral_contMDiff_smul_eq_zero (𝓡 3) hloc (fun φ hφ hc hs=>by
    let ψ:EnergyTest g.leviCivitaData univ:=⟨φ,hφ,hc,subset_univ _⟩
    have hh:inner ℝ F (toL2 g.leviCivitaData univ (ψ:H1Zero g.leviCivitaData univ))=
        inner ℝ G (toL2 g.leviCivitaData univ (ψ:H1Zero g.leviCivitaData univ)):=
      (hF ψ hs).symm.trans (hG ψ hs)
    rw [nativeL2_source_test_pairing,nativeL2_source_test_pairing] at hh
    change (∫y,φ y*(F y-G y) ∂g.volumeMeasure)=0
    calc
      _=∫y,F y*φ y-G y*φ y ∂g.volumeMeasure:=by congr 1;funext y;ring
      _=(∫y,F y*φ y ∂g.volumeMeasure)-(∫y,G y*φ y ∂g.volumeMeasure):=
        integral_sub ((Lp.memLp F).integrable_mul ψ.memLp) ((Lp.memLp G).integrable_mul ψ.memLp)
      _=0:=by rw [show (∫y,F y*φ y ∂g.volumeMeasure)=(∫y,G y*φ y ∂g.volumeMeasure) from hh];ring)
  filter_upwards [ae_restrict_of_ae (s:=Ω) hz,ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
  exact sub_eq_zero.mp (hy hyΩ)

#print axioms nativeL2_source_test_pairing
#print axioms nativeForcedEnergy_congr_source
#print axioms nativeForcedEnergy_source_unique
end Yamabe3.Analysis.SpherePolar
