import Yamabe3.Analysis.NativeSmoothOriginalExteriorAssembly
import Yamabe3.Analysis.NativeShellSourceLocalZero

/-! Actual finite shell compensation is volume-zero on the physical
entrance collar if its actual scaled rows vanish there. This is a proved
transport statement for the literal finite source, not a support label. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeFiniteCompensationSource_zero_entrance
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hKs:K⊆e.source) (a S:ℝ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (N:ℕ) (Comp:ℕ→NativeCollarL2) (f:Fin N→E→ℝ)
    (hfit:euclideanDilatedDomain a nativePoissonEntranceCollar⊆K)
    (hComp:∀i:Fin N,(Comp i:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]f i)
    (hz:∀(i:Fin N)(x:E),x∈euclideanDilatedDomain a nativePoissonEntranceCollar→
      f i (Real.exp (nativeOuterLogShellCenter i-Real.log a) • x)=0):
    nativeFiniteCompensationSourceFunction gE e K a S χ hχ N Comp
      =ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)](fun _=>0):=by
  let D:=euclideanDilatedDomain a nativePoissonEntranceCollar
  have hD:IsOpen D:=(nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹)
  have hi(i:Fin N):nativeDensityCorrectedChartSource gE e K
      (nativePhysicalShellSource a (nativeOuterLogShellCenter i)
        (nativeCollarScalarMulCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
          (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ).continuous (Comp i)))
      =ᵐ[g.volumeMeasure.restrict (e '' D)](fun _=>0):=by
    let q:=nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ
    have hq:Continuous q:=(nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ).continuous
    let U:=nativeCollarScalarMulCLM q hq (Comp i)
    have hU:(U:E→ℝ)=ᵐ[volume.restrict nativeSourceShell](fun x=>q x*f i x):=by
      have hh: (U:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar](fun x=>q x*f i x):=by
        filter_upwards [nativeCollarScalarMulCLM_ae q hq (Comp i),hComp i] with x hx hc
        exact hx.trans (congrArg (q x*·) hc)
      exact ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl) hh
    have hSource:=nativePhysicalShellSource_local_zero a (nativeOuterLogShellCenter i) U
      (fun x=>q x*f i x) hU hD.measurableSet (fun x hx _=>by rw [hz i x hx,mul_zero])
    exact nativeDensityCorrectedChartSource_local_zero g gE e he hei hKs hD hfit _ hSource
  filter_upwards [eventually_all.mpr hi] with y hy
  dsimp only [nativeFiniteCompensationSourceFunction]
  exact Finset.sum_eq_zero (fun i _=>hy i)

#print axioms nativeFiniteCompensationSource_zero_entrance
end Yamabe3.Analysis.SpherePolar
