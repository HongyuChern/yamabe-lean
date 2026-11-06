import Yamabe3.Analysis.NativeClosedJetFarSourceAlgebra
import Yamabe3.Analysis.NativeDensityPhysicalShellPairing

/-! Exact physical/spectral pairing of the full native far source.
Every finite integral is justified by the actual L2 source. The tail
reaction is retained separately, never relabelled as a compensation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem nativeClosedJetFarSource_actual_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (S:ℝ) {n:ℕ} (t:Fin n→ℝ) (C:NativeCollarL2) (G:Fin n→NativeCollarL2)
    (hfitS:∀x:E,Real.exp (S-Real.log a) • x∈nativeSourceShell→x∈K)
    (hfit:∀i:Fin n,∀x:E,Real.exp (t i-Real.log a) • x∈nativeSourceShell→x∈K)
    (q:M→ℝ) (u:H1Zero g.leviCivitaData univ)
    (hq:MemLp (fun y=>q y*toL2 g.leviCivitaData univ u y) 2 g.volumeMeasure)
    (η:EnergyTest g.leviCivitaData univ)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (htest:∀x∈K,φ (a⁻¹ • x)=η (e x)):
    (∫y,nativeClosedJetFarSource g gE e K a S t C G q u y*η y ∂g.volumeMeasure)=
      8*a*inner ℝ (nativeFullShellSourceReturnCLM S C) (nativePhysicalPairTestL2 φ hφ hc h0)+
      8*a*(∑i:Fin n,inner ℝ (nativeFullShellSourceReturnCLM (t i) (G i)) (nativePhysicalPairTestL2 φ hφ hc h0))+
      (∫y,8*(q y*toL2 g.leviCivitaData univ u y)*η y ∂g.volumeMeasure):=by
  obtain ⟨D,hD,hd⟩:=exists_nativeDensityCorrectedChart_lp_bound g gE e he hei hK hKs 2
  let ζ:M→ℝ:=(η:M→ℝ)
  let fC:M→ℝ:=nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a S C)
  let fG:Fin n→M→ℝ:=fun i=>nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a (t i) (G i))
  have hmC:MemLp fC 2 g.volumeMeasure:=(hd _ (nativePhysicalShellSource_memLp_two a S C)).1
  have hmG(i:Fin n):MemLp (fG i) 2 g.volumeMeasure:=(hd _ (nativePhysicalShellSource_memLp_two a (t i) (G i))).1
  have hmSum:MemLp (fun y=>∑i:Fin n,fG i y) 2 g.volumeMeasure:=memLp_finsetSum Finset.univ (fun i _=>hmG i)
  have hCp:=nativeDensityPhysicalShell_full_pairing g gE e he hei hK hKs hcoeff ha S C hfitS η φ hφ hc h0 htest
  have hGp(i:Fin n):(∫y,fG i y*ζ y ∂g.volumeMeasure)=8*a*inner ℝ (nativeFullShellSourceReturnCLM (t i) (G i)) (nativePhysicalPairTestL2 φ hφ hc h0):=nativeDensityPhysicalShell_full_pairing g gE e he hei hK hKs hcoeff ha (t i) (G i) (hfit i) η φ hφ hc h0 htest
  have hCint:Integrable (fun y=>fC y*ζ y) g.volumeMeasure:=hmC.integrable_mul η.memLp
  have hGint(i:Fin n):Integrable (fun y=>fG i y*ζ y) g.volumeMeasure:=(hmG i).integrable_mul η.memLp
  have hSumInt:Integrable (fun y=>(∑i:Fin n,fG i y)*ζ y) g.volumeMeasure:=hmSum.integrable_mul η.memLp
  have hQint:Integrable (fun y=>8*(q y*toL2 g.leviCivitaData univ u y)*ζ y) g.volumeMeasure:=(hq.const_mul 8).integrable_mul η.memLp
  change (∫y,fC y*ζ y ∂g.volumeMeasure)=_ at hCp
  have hsum:(∫y,(∑i:Fin n,fG i y)*ζ y ∂g.volumeMeasure)=
      8*a*(∑i:Fin n,inner ℝ (nativeFullShellSourceReturnCLM (t i) (G i)) (nativePhysicalPairTestL2 φ hφ hc h0)):=by
    calc
      _=(∑i:Fin n,∫y,fG i y*ζ y ∂g.volumeMeasure):=by
        simpa only [Pi.mul_apply,Finset.sum_mul] using
          (integral_finsetSum Finset.univ (fun (i:Fin n) _=>hGint i))
      _=(∑i:Fin n,8*a*inner ℝ (nativeFullShellSourceReturnCLM (t i) (G i)) (nativePhysicalPairTestL2 φ hφ hc h0)):=
        Finset.sum_congr rfl (fun i _=>hGp i)
      _=_:=(Finset.mul_sum _ _ _).symm
  change (∫y,(fC y+(∑i:Fin n,fG i y)+8*(q y*toL2 g.leviCivitaData univ u y))*ζ y ∂g.volumeMeasure)=_
  simp_rw [add_mul]
  calc
    _=(∫y,fC y*ζ y+(∑i:Fin n,fG i y)*ζ y ∂g.volumeMeasure)+
        (∫y,8*(q y*toL2 g.leviCivitaData univ u y)*ζ y ∂g.volumeMeasure):=by
      exact integral_add (hCint.add hSumInt) hQint
    _=((∫y,fC y*ζ y ∂g.volumeMeasure)+(∫y,(∑i:Fin n,fG i y)*ζ y ∂g.volumeMeasure))+
        (∫y,8*(q y*toL2 g.leviCivitaData univ u y)*ζ y ∂g.volumeMeasure):=
      congrArg (fun r:ℝ=>r+(∫y,8*(q y*toL2 g.leviCivitaData univ u y)*ζ y ∂g.volumeMeasure))
        (integral_add hCint hSumInt)
    _=_:=by rw [hCp,hsum]

#print axioms nativeClosedJetFarSource_actual_pairing
end Yamabe3.Analysis.SpherePolar
