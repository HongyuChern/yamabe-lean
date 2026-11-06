import Yamabe3.Analysis.NativeFixedFarL2Source
import Yamabe3.Analysis.NativeDensityPhysicalShellPairing

/-! A fixed finite family of actual shell rows constructs ONE native
L2 source BEFORE all tests, with its complete physical/spectral pairing.
No test-dependent compensation representative is chosen. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem exists_nativeFiniteShell_fixed_native_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (n:ℕ) (t:Fin n→ℝ) (U:Fin n→NativeCollarL2)
    (hfit:∀i:Fin n,∀y:E,Real.exp (t i-Real.log a) • y∈nativeSourceShell→y∈K):
    ∃C:Lp ℝ 2 g.volumeMeasure,
      (C:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>∑i:Fin n,
        nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a (t i) (U i)) y) ∧
      ∀(η:EnergyTest g.leviCivitaData univ)(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)
        (hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        (∀y∈K,φ (a⁻¹ • y)=η (e y)) →
        inner ℝ C (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))=
          8*a*(∑i:Fin n,inner ℝ (nativeFullShellSourceReturnCLM (t i) (U i))
            (nativePhysicalPairTestL2 φ hφ hc h0)):=by
  let f:Fin n→M→ℝ:=fun i=>nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a (t i) (U i))
  have hm:MemLp (fun y=>∑i:Fin n,f i y) 2 g.volumeMeasure:=
    nativeDensityShell_finite_memLp_two g gE e he hei hK hKs n a t U
  let C:=hm.toLp (fun y=>∑i:Fin n,f i y)
  have hC:(C:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>∑i:Fin n,f i y):=hm.coeFn_toLp
  refine ⟨C,hC,fun η φ hφ hc h0 htest=>?_⟩
  obtain ⟨D,hD,hd⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  have hmi(i:Fin n):MemLp (f i) 2 g.volumeMeasure:=(hd _ (nativePhysicalShellSource_memLp_two a (t i) (U i))).1
  have hi(i:Fin n):Integrable (fun y=>f i y*η y) g.volumeMeasure:=(hmi i).integrable_mul η.memLp
  have hp(i:Fin n):(∫y,f i y*η y ∂g.volumeMeasure)=
      8*a*inner ℝ (nativeFullShellSourceReturnCLM (t i) (U i)) (nativePhysicalPairTestL2 φ hφ hc h0):=
    nativeDensityPhysicalShell_full_pairing g gE e he hei hK hKs hcoeff ha (t i) (U i) (hfit i) η φ hφ hc h0 htest
  calc
    _=(∫y,(∑i:Fin n,f i y)*η y ∂g.volumeMeasure):=by
      rw [L2.inner_def,toL2_coe]
      apply integral_congr_ae
      filter_upwards [hC,η.memLp.coeFn_toLp] with y hy hη
      simp only [Real.inner_apply]
      change (C:M→ℝ) y*(η.memLp.toLp η) y=_
      exact congrArg₂ (·*·) hy hη
    _=(∑i:Fin n,∫y,f i y*η y ∂g.volumeMeasure):=by
      simpa only [Pi.mul_apply,Finset.sum_mul] using integral_finsetSum Finset.univ (fun (i:Fin n) _=>hi i)
    _=(∑i:Fin n,8*a*inner ℝ (nativeFullShellSourceReturnCLM (t i) (U i)) (nativePhysicalPairTestL2 φ hφ hc h0)):=
      Finset.sum_congr rfl (fun i _=>hp i)
    _=_:=(Finset.mul_sum _ _ _).symm

#print axioms exists_nativeFiniteShell_fixed_native_source
end Yamabe3.Analysis.SpherePolar
