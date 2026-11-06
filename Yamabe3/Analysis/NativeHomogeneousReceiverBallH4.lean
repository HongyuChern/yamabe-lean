import Yamabe3.Analysis.NativeJacobianAnnularSobolev
import Yamabe3.Analysis.SmoothDilationBallJets

/-! Uniform whole-ball H4 control of the genuine native homogeneous
conformal-Laplacian field, including its regular centre. An annular
estimate cannot supply the centre or returning entrance jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "RcvA" => ball (0:E) 3
local notation "RcvV" => ball (0:E) 2
local notation "RcvW" => ball (0:E) 1
variable {M:Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativeHomogeneous_receiver_ball_H4_bound
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1) :
    ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀R:ℝ,0<R →
      closedBall (0:E) R⊆e.source →
      (∀x∈closedBall (0:E) R,gE.euclideanCoefficients x=g.pullbackCoefficients e x) →
      ∀r:ℝ,0<r → r<δ → r*3<R → ∀u:M → ℝ,
      (∀x∈ball (0:E) R,ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) ∞ u (e x)) → 
      (∀x∈ball (0:E) R,-8*g.leviCivitaData.laplacian u (e x)+
        g.leviCivitaData.scalarCurvature (e x)*u (e x)=0) → 
      derivativeProfile 2 RcvW 4 (fun z=>u (e (r • z)))≤
        ENNReal.ofReal C*eLpNorm (fun z=>u (e (r • z))) 2 (volume.restrict RcvV) := by
  have hVc:IsCompact (closure RcvV):=by rw [closure_ball (0:E) (by norm_num:(2:ℝ)≠0)];exact isCompact_closedBall _ _
  have hWc:IsCompact (closure RcvW):=by rw [closure_ball (0:E) (by norm_num:(1:ℝ)≠0)];exact isCompact_closedBall _ _
  have hVA:closure RcvV⊆RcvA:=by
    rw [closure_ball (0:E) (by norm_num:(2:ℝ)≠0)]
    exact closedBall_subset_ball (by norm_num)
  have hWV:closure RcvW⊆RcvV:=by
    rw [closure_ball (0:E) (by norm_num:(1:ℝ)≠0)]
    exact closedBall_subset_ball (by norm_num)
  have hV4:closure RcvV⊆ball (0:E) 4:=hVA.trans (ball_subset_ball (by norm_num))
  obtain ⟨δa,hδa,L,hL,hmat⟩:=exists_uniform_native_rescaled_bilinear_forms gE hB hρ 4 (by norm_num:(0:ℝ)<4)
  obtain ⟨Q,hQ,hqjet⟩:=exists_smooth_dilation_ball_jets (contDiff_nativePotentialDensity gE) 2 (by norm_num:(0:ℝ)≤3)
  obtain ⟨C,hC,hest⟩:=exists_local_uniform_derivativeProfile_add_two_with_potential 2
    isOpen_ball isOpen_ball hVc hVA hV4 isOpen_ball hWc hWV (by norm_num:(0:ℝ)<1/2) hL hQ
  refine ⟨min 1 δa,C,lt_min zero_lt_one hδa,hC,?_⟩
  intro R hR hsource hcoeff r hr hrδ hrR u hu hP
  have hr1:r≤1:=(hrδ.trans_le (min_le_left _ _)).le
  have hra:r<δa:=hrδ.trans_le (min_le_right _ _)
  let O:=ball (0:E) R
  have hOs:O⊆e.source:=ball_subset_closedBall.trans hsource
  have hOc:∀x∈O,gE.euclideanCoefficients x=g.pullbackCoefficients e x:=fun x hx=>hcoeff x (ball_subset_closedBall hx)
  have hmap:MapsTo (fun z:E=>r • z) RcvA O:=by
    intro z hz
    have hz3:‖z‖<3:=by simpa using hz
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left hz3 hr).trans hrR
  have hus:ContDiffOn ℝ ∞ (fun z=>u (e (r • z))) RcvA:=
    (contDiffOn_native_chart_representative e he hOs hu).comp
      (contDiff_id.const_smul r).contDiffOn hmap
  let q:=rescaledNativeJacobianPotential gE r (fun _:E=>0)
  have heq:q=(-r^2) • (fun y:E=>nativePotentialDensity gE (r • y)):=by
    funext y
    simp only [q,rescaledNativeJacobianPotential,nativePotentialDensity,Pi.smul_apply,smul_eq_mul]
    ring
  have hqs:ContDiffOn ℝ ∞ q RcvA:=by
    rw [heq]
    exact (contDiff_const.smul ((contDiff_nativePotentialDensity gE).comp (contDiff_id.const_smul r))).contDiffOn
  have hqj:∀n≤2,∀z∈RcvV,‖iteratedFDeriv ℝ n q z‖≤Q:=by
    intro n hn z hz
    have hpot:ContDiffAt ℝ n (fun y:E=>nativePotentialDensity gE (r • y)) z:=
      ((contDiff_nativePotentialDensity gE).comp (contDiff_id.const_smul r)).contDiffAt.of_le (by exact_mod_cast le_top)
    rw [heq,iteratedFDeriv_const_smul_apply hpot,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg r)]
    have hz3:z∈closedBall (0:E) 3:=by
      exact ball_subset_closedBall ((ball_subset_ball (by norm_num:(2:ℝ)≤3)) hz)
    exact (mul_le_mul le_rfl (hqjet r ⟨hr.le,hr1⟩ n hn z hz3) (norm_nonneg _) (sq_nonneg r)).trans
      (mul_le_of_le_one_left hQ (pow_le_one₀ hr.le hr1))
  obtain ⟨B,hBa,hBlam,hBj,hBosc⟩:=hmat r hr.le hra
  have hVball:RcvV⊆ball (0:E) 4:=subset_closure.trans hV4
  have hP':∀x∈O,-8*g.leviCivitaData.laplacian u (e x)+
      (g.leviCivitaData.scalarCurvature (e x)-30*(0:ℝ)^4)*u (e x)=0:=by
    simpa only [zero_pow (by decide:4≠0),mul_zero,sub_zero] using hP
  have hweak:WeakEquation RcvV (matrixFlux B.a (fun j=>partialDeriv j (fun z=>u (e (r • z)))))
      (fun z=>(0:ℝ)+q z*u (e (r • z))):=by
    rw [hBa]
    simpa [q,rescaledNativeJacobianPotential] using native_jacobian_rescaled_weak_equation g gE
      g.leviCivitaData gE.leviCivitaData e he hei (u:=fun _:M => 0) (W:=u) (F:=fun _:M => 0) isOpen_ball isOpen_ball isOpen_ball hVc hVA hOs hOc hu hP' r hmap
  have hh:=hest B (by rw [hBlam]) (fun n hn z hz i j=>hBj n hn z (hVball hz) i j)
    (fun z hz=>hBosc z (hVball hz)) q hqs hqj hus contDiffOn_const hweak
  have hz:derivativeProfile 2 RcvV 2 (fun _:E=>0)=0:=by simp [derivativeProfile]
  simpa only [hz,add_zero,derivativeProfile_zero] using hh

#print axioms exists_nativeHomogeneous_receiver_ball_H4_bound
end Yamabe3.Analysis.SpherePolar
