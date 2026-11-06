import Yamabe3.Analysis.BubbleLowJacobiFunctions
import Yamabe3.Analysis.NativeFiniteLowProjection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Fixed genuine annular compensations chi Z_i and their positive
Gram diagonal, for the actual finite low angular eigenspace. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm

def bubbleLowJacobi (i:AngularIndex):ℝ→ℝ:=
  if angularEigenvalue i=0 then bubbleLowRadial else bubbleLowTranslation

theorem bubbleLowJacobi_smooth (i:AngularIndex):ContDiff ℝ ∞ (bubbleLowJacobi i):=by
  unfold bubbleLowJacobi
  split_ifs <;> first | exact bubbleLowRadial_smooth | exact bubbleLowTranslation_smooth

theorem bubbleLowJacobi_equation (i:AngularIndex) (hi:i∈nativeLowIndexFinset) (t:ℝ):
    deriv (deriv (bubbleLowJacobi i)) t-(1/4+angularEigenvalue i)*bubbleLowJacobi i t+
      (15/4)*fullBubbleDensity t*bubbleLowJacobi i t=0:=by
  have hlo:=(mem_nativeLowIndexFinset i).mp hi
  rcases angularEigenvalue_zero_two_or_ge_six i with h0|h2|h6
  · simpa only [bubbleLowJacobi,h0,ite_true,add_zero] using bubbleLowRadial_equation t
  · simpa only [bubbleLowJacobi,h2,show ¬(2:ℝ)=0 by norm_num,ite_false] using bubbleLowTranslation_equation t
  · exact (not_lt_of_ge h6 hlo).elim

theorem bubbleLowJacobi_entrance_ne_zero (i:AngularIndex) {t:ℝ} (ht:0<t):
    bubbleLowJacobi i t≠0:=by
  unfold bubbleLowJacobi
  split_ifs
  · exact bubbleLowRadial_ne_zero_after_peak ht
  · exact bubbleLowTranslation_ne_zero t

private theorem bubbleLowJacobi_at_minus_one_ne_zero (i:AngularIndex):bubbleLowJacobi i (-1)≠0:=by
  unfold bubbleLowJacobi
  split_ifs
  · apply mul_ne_zero (bubbleExpPower_pos _ _ _).ne'
    have he:Real.exp (2*(-1:ℝ))<1:=Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  · exact bubbleLowTranslation_ne_zero _

def bubbleCompensationCutoff : ContDiffBump (-1:ℝ):=⟨1/4,1/2,by norm_num,by norm_num⟩

def bubbleCompensation (i:AngularIndex) (t:ℝ):ℝ:=bubbleCompensationCutoff t*bubbleLowJacobi i t

def bubbleCompensationMass (i:AngularIndex):ℝ:=∫t:ℝ,bubbleLowJacobi i t*bubbleCompensation i t

theorem bubbleCompensation_smooth_compact (i:AngularIndex):
    ContDiff ℝ ∞ (bubbleCompensation i) ∧ HasCompactSupport (bubbleCompensation i):=
  ⟨bubbleCompensationCutoff.contDiff.mul (bubbleLowJacobi_smooth i),bubbleCompensationCutoff.hasCompactSupport.mul_right⟩

theorem bubbleCompensation_zero_of_nonneg (i:AngularIndex) {t:ℝ} (ht:0≤t):
    bubbleCompensation i t=0:=by
  have hz:bubbleCompensationCutoff t=0:=bubbleCompensationCutoff.zero_of_le_dist (by
    change (1/2:ℝ)≤dist t (-1)
    rw [Real.dist_eq,abs_of_nonneg (by linarith)]
    linarith)
  simp only [bubbleCompensation,hz,zero_mul]

theorem bubbleCompensationMass_pos (i:AngularIndex):0<bubbleCompensationMass i:=by
  have hc:Continuous (fun t:ℝ=>bubbleLowJacobi i t*bubbleCompensation i t):=
    (bubbleLowJacobi_smooth i).continuous.mul (bubbleCompensation_smooth_compact i).1.continuous
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x:=(-1:ℝ))
    (bubbleCompensation_smooth_compact i).2.mul_left
    (fun t=>by
      change 0≤bubbleLowJacobi i t*(bubbleCompensationCutoff t*bubbleLowJacobi i t)
      nlinarith [mul_nonneg (bubbleCompensationCutoff.nonneg' t) (sq_nonneg (bubbleLowJacobi i t))])
  have hχ:bubbleCompensationCutoff (-1)=1:=bubbleCompensationCutoff.one_of_mem_closedBall (by
    change (-1:ℝ)∈closedBall (-1) (1/4)
    simp)
  simpa only [bubbleCompensation,hχ,one_mul] using mul_ne_zero
    (bubbleLowJacobi_at_minus_one_ne_zero i) (bubbleLowJacobi_at_minus_one_ne_zero i)

theorem bubbleCompensationMass_truncated (i:AngularIndex) {t₀:ℝ} (ht:0≤t₀):
    (∫t in Iic t₀,bubbleLowJacobi i t*bubbleCompensation i t)=bubbleCompensationMass i:=by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t h
  have hpos:0≤t:=ht.trans (le_of_lt (lt_of_not_ge h))
  rw [bubbleCompensation_zero_of_nonneg i hpos,mul_zero]

theorem actual_angular_representative_pairing (i j:AngularIndex):
    (∫θ:S,angularRepresentative i θ*angularRepresentative j θ ∂(roundSphereMetric 2).volumeMeasure)=
      if i=j then (1:ℝ) else 0:=by
  classical
  have he:(∫θ:S,angularRepresentative i θ*angularRepresentative j θ ∂(roundSphereMetric 2).volumeMeasure)=
      inner ℝ (angularBasis i) (angularBasis j):=by
    rw [L2.inner_def]
    simp only [Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [angularRepresentative_ae i,angularRepresentative_ae j] with θ hi hj
    rw [hi,hj]
    simp only [RCLike.inner_apply,conj_trivial]
    ring
  rw [he]
  exact orthonormal_iff_ite.mp angularBasis.orthonormal i j

theorem actual_bubble_compensation_gram (i j:AngularIndex) {t₀:ℝ} (ht:0≤t₀):
    (∫t in Iic t₀,∫θ:S,
      (bubbleLowJacobi i t*angularRepresentative i θ)*
        (bubbleCompensation j t*angularRepresentative j θ) ∂(roundSphereMetric 2).volumeMeasure)=
      if i=j then bubbleCompensationMass i else 0:=by
  classical
  have hinner (t:ℝ):(∫θ:S,(bubbleLowJacobi i t*angularRepresentative i θ)*
      (bubbleCompensation j t*angularRepresentative j θ) ∂(roundSphereMetric 2).volumeMeasure)=
      bubbleLowJacobi i t*bubbleCompensation j t*(if i=j then 1 else 0):=by
    rw [←actual_angular_representative_pairing,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun θ=>by ring
  simp_rw [hinner]
  by_cases hij:i=j
  · subst j
    simpa using bubbleCompensationMass_truncated i ht
  · simp [hij]

def bubbleLowCauchyCompensation (i:AngularIndex) (t₀ d n b:ℝ):ℝ:=
  (-bubbleLowJacobi i t₀*n+deriv (bubbleLowJacobi i) t₀*d-b)/bubbleCompensationMass i

theorem bubbleLowCauchyCompensation_equation (i:AngularIndex) (t₀ d n b:ℝ):
    bubbleCompensationMass i*bubbleLowCauchyCompensation i t₀ d n b=
      -bubbleLowJacobi i t₀*n+deriv (bubbleLowJacobi i) t₀*d-b:=by
  unfold bubbleLowCauchyCompensation
  field_simp [(bubbleCompensationMass_pos i).ne']

#print axioms bubbleLowJacobi_equation
#print axioms bubbleLowJacobi_entrance_ne_zero
#print axioms bubbleCompensation_smooth_compact
#print axioms bubbleCompensationMass_pos
#print axioms bubbleCompensationMass_truncated
#print axioms actual_bubble_compensation_gram
#print axioms bubbleLowCauchyCompensation_equation
end Yamabe3.Analysis.Delaunay
