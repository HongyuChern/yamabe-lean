import Yamabe3.Analysis.NativeSupportedOuterNewtonAnnulus
import Yamabe3.Analysis.WeakCutoffCriticalGlobal

/-! A genuine small far-cutoff physical residual from the same complete
Newton-decaying outer field. Its critical norm is sqrt(a)*exp(s/2),
including physical factor eight, rather than the earlier coarse sqrt(a). -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem exists_nativeSupportedOuter_Newton_cutoff_bound
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (b : ℝ) {τ : ℝ} (ht : 0 < τ) :
    ∃T : ℝ, T ≤ -(1/2 : ℝ) ∧ ∃C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
        (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt : ℝ ∂volume, t < b → F t=0) →
      ∃w : ℝ×S → ℝ, Measurable w ∧
        (∀t,(fun θ => w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t : S → ℝ)) ∧
        (∀s : ℝ, NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        ∀(s a : ℝ), s ≤ T → 0 < a →
          let Ephys := physicalCutoffSource halfEndBasicAnnulus χ
            (weightedPhysicalDilation s (cylinderLift w)) s a
          MemLp Ephys (6/5 : ℝ≥0∞) volume ∧
            eLpNorm Ephys (6/5 : ℝ≥0∞) volume ≤
              C*ENNReal.ofReal (Real.sqrt a*Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  obtain ⟨T,hT,C₀,hC₀,h⟩ := exists_nativeSupportedOuter_same_field_Newton_annulus_H4 b ht
  have hc : IsCompact (closure halfEndBasicAnnulus) := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
    apply Bornology.IsBounded.closure
    exact (Metric.isBounded_ball (x := (0 : E)) (r := 2)).subset (fun x hx => by simpa using hx.2)
  obtain ⟨D,hD,hd⟩ := exists_weakCutoff_global_physical_critical_bound halfEndBasicAnnulus_isOpen hc χ hχ
  refine ⟨T,hT,D*C₀,by finiteness,fun F d n σ hσ hF => ?_⟩
  obtain ⟨w,hw,hl,ha,hj,hreg⟩ := h F d n σ hσ hF
  refine ⟨w,hw,ha,hj,fun s a hs ha' => ?_⟩
  have hh := hreg s hs
  have hu := hh.1.le_of_le (by norm_num : 1 ≤ 4)
  have hn : iteratedWeakSobolevNorm 1 2 (weightedPhysicalDilation s (cylinderLift w)) halfEndBasicAnnulus ≤
      ENNReal.ofReal (Real.exp (2*s))*(C₀*ENNReal.ofReal (Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖))) := by
    apply (hh.2 1 (by norm_num)).trans_eq
    have he : Real.exp (5*s/2)=Real.exp (2*s)*Real.exp (s/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he,mul_assoc,ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  have hr := hd _ hu (C₀*ENNReal.ofReal (Real.exp (s/2)*(‖(F,(d,n))‖+‖σ‖))) s a ha' hn
  refine ⟨hr.1,hr.2.trans_eq ?_⟩
  rw [mul_assoc (Real.sqrt a),ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  ring

#print axioms exists_nativeSupportedOuter_Newton_cutoff_bound
end Yamabe3.Analysis.SpherePolar
