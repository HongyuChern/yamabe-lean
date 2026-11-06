import Yamabe3.Analysis.NativeHomogeneousCoreWeakSource
import Yamabe3.Analysis.NativeScaledSmoothOperator
import Yamabe3.Analysis.NativeCoreUnitOperator
import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The ACTUAL affine original-source feedback has the required inner
fixed point, since its incoming source has exactly zero first coordinate.
This discharges the partial inner cancellation premise without assuming
an obsolete full-collar exterior fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)


theorem nativeActualCore_same_completed_operator_source
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (F:E→ℝ) (hF:ContDiff ℝ ∞ F)
    (hrep:∀x∈closedBall (0:E) 4,F=ᶠ[𝓝 x]
      (fun y=>nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R (e (a • y)))):
    ∃ψ:EnergyTest g.leviCivitaData univ,
      (ψ:H1Zero g.leviCivitaData univ)=
        energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val ∧
      (ψ:M→ℝ)=coordinateExtension e (fun x:E=>χin (a⁻¹ • x)*F (a⁻¹ • x)) ∧
      (∀x∈ball (0:E) 4,nativeCoreUnitOperator gE a χin F x=
        (a^2*gE.pullbackVolumeDensity id (a • x)/8)*
          (-8*g.leviCivitaData.laplacian ψ (e (a • x))+
            g.leviCivitaData.scalarCurvature (e (a • x))*ψ (e (a • x)))) ∧
      ∃Fcore:Lp ℝ 2 g.volumeMeasure,
        (Fcore:M→ℝ)=ᵐ[g.volumeMeasure](fun x=>-8*g.leviCivitaData.laplacian ψ x+
          g.leviCivitaData.scalarCurvature x*ψ x) ∧
        ∀η:H1Zero g.leviCivitaData univ,
          closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
            (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val) η=
              inner ℝ Fcore (toL2 g.leviCivitaData univ η):=by
  let U:=nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R
  have hfit4:euclideanDilatedDomain a (ball (0:E) 4)⊆closedBall (0:E) R₀:=by
    apply euclideanDilatedBall_subset_closedBall ha
    have hh:=W.receiving_fit
    linarith
  have hfit3:euclideanDilatedDomain a (ball (0:E) 3)⊆e.source:=
    ((preimage_mono (ball_subset_ball (by norm_num:(3:ℝ)≤4))).trans hfit4).trans hsource
  have hcore:tsupport (W.core:M→ℝ)⊆e '' ball (0:E) (a*64):=by
    rw [W.core_coordinate]
    have hc:HasCompactSupport (fun x:E=>χin (a⁻¹ • x)):=
      W.inner_compact.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))
    have hs:tsupport (fun x:E=>χin (a⁻¹ • x))⊆euclideanDilatedDomain a (ball (0:E) 3):=by
      change tsupport (χin ∘ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne') : E≃ₜE))⊆_
      rw [tsupport_comp_eq_preimage χin (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))]
      exact preimage_mono W.inner_support
    apply (tsupport_coordinateExtension_subset_image e hc (hs.trans hfit3)).trans
    apply image_mono
    intro x hx
    have hn:=mem_ball_zero_iff.mp (hs hx)
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le] at hn
    rw [mem_ball_zero_iff]
    have hn':‖x‖<a*3:=(inv_mul_lt_iff₀ ha).mp hn
    nlinarith
  obtain ⟨ψ,hψ,hψH,Fcore,hFcore,hweak⟩:=nativeHomogeneousCore_actual_source g (fun _:M=>0) contMDiff_const
    W.open_domain W.core hcore R
  have hcoord:(ψ:M→ℝ)=coordinateExtension e (fun x:E=>χin (a⁻¹ • x)*F (a⁻¹ • x)):=by
    funext y
    change ψ y=_
    rw [show ψ y=W.core y*U y from congrFun hψ y,W.core_coordinate]
    by_cases hy:y∈e.target
    · rw [coordinateExtension_apply e _ hy,coordinateExtension_apply e _ hy]
      let x:=a⁻¹ • e.symm y
      change χin x*U y=χin x*F x
      by_cases hz:χin x=0
      · rw [hz,zero_mul,zero_mul]
      · have hx:x∈closedBall (0:E) 4:=
          ball_subset_closedBall ((ball_subset_ball (by norm_num:(3:ℝ)≤4))
            (W.inner_support (subset_tsupport χin (Function.mem_support.mpr hz))))
        have hv: F x=U y:=by
          have hh:=(hrep x hx).self_of_nhds
          change F x=U (e (a • x)) at hh
          simpa only [x,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,e.right_inv hy] using hh
        rw [hv]
    · simp only [coordinateExtension,indicator_of_notMem hy,zero_mul]
  have hunit(x:E)(hx:x∈ball (0:E) 4):
      (fun y=>χin y*F y)=ᶠ[𝓝 x](fun y=>ψ (e (a • y))):=by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hys:a • y∈e.source:=by
      apply hsource (hfit4 ?_)
      change a⁻¹ • (a • y)∈ball (0:E) 4
      simpa only [smul_smul,inv_mul_cancel₀ ha.ne',one_smul] using hy
    rw [hcoord,coordinateExtension_comp_apply e _ hys]
    simp only [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
  refine ⟨ψ,hψH,hcoord,fun x hx=>?_,Fcore,?_,hweak⟩
  · exact nativeScaledSmoothTest_operator_identity g gE e he hei hsource hcoeff ha isOpen_ball hfit4
      ψ (fun y=>χin y*F y) (hχin.mul hF) hunit hx
  · simpa only [zero_pow (by decide:(4:ℕ)≠0),mul_zero,sub_zero] using hFcore

#print axioms nativeActualCore_same_completed_operator_source
end Yamabe3.Analysis.SpherePolar
