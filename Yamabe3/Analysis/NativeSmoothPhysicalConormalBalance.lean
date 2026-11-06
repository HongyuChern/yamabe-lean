import Yamabe3.Analysis.NativeConormalPotentialChange
import Yamabe3.Analysis.NativeForcedEnergyDataMembership

/-! The actual exterior conormal on the genuine physical trace quotient
matches the inward source-subtracted energy for the SAME completed field.
The smooth exterior operator/source adjustment is explicit and proved.
Normal-chart trace calibration is exactly the existing trace interface. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss:∀x v:E,gE.inner x x v=inner ℝ x v)
    {a Cρ:ℝ} (ha:0<a) (hs:closedBall (0:E) (2*a)⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) (2*a),gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hCρ:0≤Cρ) (hρ:∀θ:SpherePolar.S,gE.pullbackVolumeDensity id (a • (θ:E))≤Cρ)
local notation "hAnn" => (fun (x:E) (hx:x∈sphereTraceAnnulus a (2*a))=>hs
  (show x∈closedBall (0:E) (2*a) by simpa only [mem_closedBall,dist_zero_right] using hx.2))
local notation "hr" => (show a∈Icc a (2*a) from ⟨le_rfl,by linarith only [ha]⟩)
local notation "hab" => (show a<2*a from by linarith only [ha])
local notation "Trace" => nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hAnn hCρ
  (fun θ=>hcoeff _ (by
    rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]
    linarith only [ha])) (fun θ=>hGauss (a • (θ:E))) hρ
local notation "Ω" => (e '' closedBall (0:E) a)ᶜ

theorem nativeSmoothGlobal_physical_conormal_balance
    (q:M→ℝ) (hq:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ q)
    (Z:H1Zero g.leviCivitaData univ) (Fg Comp:Lp ℝ 2 g.volumeMeasure)
    (hGlobal:(Z,Fg)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const univ)
    (hSrc:(Fg:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]
      (fun y=>Comp y+8*q y*toL2 g.leviCivitaData univ Z y))
    (hData:(Z,Comp)∈NativeWeakEllipticDataSpace g Ω
      (fun y=>g.leviCivitaData.scalarCurvature y-8*q y)
      (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hq))):
    ∀η:H1Zero g.leviCivitaData univ,
      EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hs hcoeff hCρ hρ
        (fun y=>g.leviCivitaData.scalarCurvature y-8*q y)
        (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hq)) ⟨(Z,Comp),hData⟩
        (HilbertTraceQuotient.quotientMap Trace η)+
      nativeWeakEnergySourceDataCLM g Ωᶜ (nativeJacobianPotential g (fun _:M=>0))
        (nativeJacobianPotential_smooth g contMDiff_const) (Z,Fg) η=0:=by
  intro η
  rw [EuclideanSphereTrace.nativeWeakPhysicalConormal_quotientMap g gE e he hei hGauss ha hs hcoeff hCρ hρ]
  have hΩ:MeasurableSet Ω:=((isCompact_closedBall (0:E) a).image_of_continuousOn
    (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  have hChange:(Comp:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]
      (fun y=>Fg y+((g.leviCivitaData.scalarCurvature y-8*q y)-nativeJacobianPotential g (fun _:M=>0) y)*
        toL2 g.leviCivitaData univ Z y):=by
    filter_upwards [hSrc] with y hy
    rw [hy]
    simp only [nativeJacobianPotential,zero_pow (by decide:(4:ℕ)≠0),mul_zero,sub_zero]
    ring
  rw [nativeWeakConormal_change_potential g Ω (nativeJacobianPotential g (fun _:M=>0))
    (fun y=>g.leviCivitaData.scalarCurvature y-8*q y)
    (nativeJacobianPotential_smooth g contMDiff_const)
    (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hq)) Z Fg Comp hChange η]
  exact nativeForcedGlobal_actual_conormal_balance g Ω hΩ Z Fg hGlobal η

#print axioms nativeSmoothGlobal_physical_conormal_balance
end Yamabe3.Analysis.SpherePolar
