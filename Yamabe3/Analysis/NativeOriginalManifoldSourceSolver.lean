import Yamabe3.Analysis.NativeChartOperatorC2

/-! Actual same-source C2 native-manifold field and its actual sphere
Cauchy data, produced from the bounded H2-to-H4 geometric solver. The
finite low entrance is retained, not asserted to vanish or match an
exterior field. All coefficients, phase, source and radius are literal. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar EuclideanSphereTrace ChartOperatorTransfer NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Euclidean
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E3) 1 \ {(0:E3)}
local notation "P" => ({(0:E3)}ᶜ:Set E3)
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

theorem exists_uniform_original_manifold_same_source_solver
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1)
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E3)
    (e:OpenPartialHomeomorph E3 M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hs:closedBall (0:E3) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E3) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ)
    (hρ:gE.pullbackVolumeDensity id 0=1):
    ∃C δ:ℝ,0≤C ∧ 0<δ ∧ δ≤R₀ ∧ ∀ε:ℝ,0<ε→ε<δ→∀p:DelaunayPhaseData κ,
      ∃(R:HalfEndPhysicalH2SourceGraph→L[ℝ]HalfEndPhysicalH4Graph)
        (Err:HalfEndPhysicalH4Graph→L[ℝ]HalfEndPhysicalH2SourceGraph),
        ‖R‖≤C ∧
        (∀(v:HalfEndPhysicalH4Graph)(x:HalfEndSourceEntrance),
          halfEndPhysicalH2SourceGraphValue (Err v) x=nativeNormalizedFullError gE ε p.orbit p.phase
            (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x) ∧
        ∀f:HalfEndPhysicalH2SourceGraph,
          ∃F:E3→ℝ,Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0=0 ∧
            EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (R f))) F (closedBall (0:E3) 4) ∧
            (F =ᵐ[volume.restrict O] fullModelPhysicalField hκ0 hκ1 p (f-Err (R f))) ∧
            (∀b:E3,‖b‖=1→F b=fullModelEntranceLift p (f-Err (R f)) b) ∧
            let W:=coordinateExtension e (fun y:E3=>F (ε⁻¹ • y))
            (∀U:Set E3,IsOpen U→IsCompact (closure U)→closure U⊆O→
              MemWkp 4 2 F U ∧
              (fun x=>ε^2*g.pullbackVolumeDensity e (ε • x)*
                (-8*g.leviCivitaData.laplacian W (e (ε • x))+
                  (g.leviCivitaData.scalarCurvature (e (ε • x))-
                    30*radialProfile p.orbit (p.phase+Real.log ε) ‖ε • x‖^4)*W (e (ε • x))))
                =ᵐ[volume.restrict U]
                halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)) ∧
            (∀θ:EuclideanSphereTrace.S,W (e (ε • (θ:E3)))=F θ) ∧
            (∀θ:EuclideanSphereTrace.S,ε*nativeExteriorNormalFluxFunction e ε W θ=-8*fderiv ℝ F (θ:E3) (θ:E3)) ∧
            Continuous (nativeExteriorNormalFluxFunction e ε W):=by
  obtain ⟨C,δ,hC,hδ,hR⟩:=exists_uniform_actual_native_same_source_solver hκ0 hκ1
    ({()}:Finset Unit) (fun _=>gE) (fun _ _=>hB) (fun _ _=>hρ)
  refine ⟨C,min δ R₀,hC,lt_min hδ hR₀,min_le_right _ _,?_⟩
  intro ε hε hεδ p
  have hεδ₁:ε<δ:=lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεR:ε<R₀:=lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨R,Err,hRC,hErr,hRf⟩:=hR ε hε hεδ₁ () (by simp) p
  refine ⟨R,Err,hRC,hErr,?_⟩
  intro f
  obtain ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,hFp⟩:=hRf f
  refine ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,?_⟩
  dsimp only
  have hSphere(θ:EuclideanSphereTrace.S):ε • (θ:E3)∈e.source:=by
    apply hs
    simpa only [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial θ hε.le] using hεR.le
  obtain ⟨hv,hn,hNc,_⟩:=same_scaled_C2_native_cauchy g e he hei hε hSphere hF2
  refine ⟨?_,hv,hn,hNc⟩
  intro U hU hUc hUO
  obtain ⟨hF4,heq⟩:=hFp U hU hUc hUO
  refine ⟨hF4,?_⟩
  filter_upwards [heq,ae_restrict_mem hU.measurableSet] with x heqx hx
  have hxO:=hUO (subset_closure hx)
  have hx0:x≠0:=hxO.2
  have hxb:ε • x∈ball (0:E3) R₀:=by
    have hxn:‖x‖<1:=by simpa only [mem_ball,dist_zero_right] using hxO.1
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    exact (mul_lt_of_lt_one_right hε hxn).trans hεR
  have htr:=same_scaled_field_original_manifold_jacobian_C2 g gE e he hei
    isOpen_ball (ball_subset_closedBall.trans hs)
    (fun y hy=>hcoeff y (ball_subset_closedBall hy)) p.orbit p.phase hε hxb hx0
    (hF2.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0))
  have hflat:=native_same_scaled_field_actual_jacobian gE p.orbit p.phase hε
    (hF2.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0)) hx0
  dsimp only at htr
  rw [hflat] at htr
  nlinarith only [htr,heqx]

#print axioms exists_uniform_original_manifold_same_source_solver
end Yamabe3.Analysis.UniformElliptic
