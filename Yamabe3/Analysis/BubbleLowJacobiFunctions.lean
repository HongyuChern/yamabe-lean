import Yamabe3.Analysis.NativeBubbleHighPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Explicit regular full-bubble low Jacobi fields for the actual
potential (15/4) sech(t)^2. These will supply the compensation pairing;
no invertible low-mode boundary matrix is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

def bubbleExpPower (a b t:ℝ):ℝ:=Real.exp (a*t)*(1+Real.exp (2*t))^b

def bubbleLogSlope (a b t:ℝ):ℝ:=a+2*b*Real.exp (2*t)/(1+Real.exp (2*t))

theorem bubbleExpPower_smooth (a b:ℝ):ContDiff ℝ ∞ (bubbleExpPower a b):=by
  apply (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
  exact (contDiff_const.add (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).rpow_const_of_ne
    (fun t=>show (1+Real.exp (2*t))≠0 from ne_of_gt (by positivity))

theorem bubbleExpPower_pos (a b t:ℝ):0<bubbleExpPower a b t:=by
  unfold bubbleExpPower
  positivity

theorem bubbleExpPower_hasDerivAt (a b t:ℝ):
    HasDerivAt (bubbleExpPower a b) (bubbleExpPower a b t*bubbleLogSlope a b t) t:=by
  have hd:0<1+Real.exp (2*t):=by positivity
  have he:=((hasDerivAt_id t).const_mul 2).exp
  have hp:=((hasDerivAt_const t (1:ℝ)).add he).rpow_const (p:=b) (Or.inl hd.ne')
  have h:=(((hasDerivAt_id t).const_mul a).exp).mul hp
  apply h.congr_deriv
  simp only [id_eq,bubbleExpPower,bubbleLogSlope,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
  rw [Real.rpow_sub_one hd.ne']
  ring

theorem bubbleLogSlope_hasDerivAt (a b t:ℝ):
    HasDerivAt (bubbleLogSlope a b) (4*b*Real.exp (2*t)/(1+Real.exp (2*t))^2) t:=by
  have hd:0<1+Real.exp (2*t):=by positivity
  have he:=((hasDerivAt_id t).const_mul 2).exp
  have h:=(hasDerivAt_const t a).add ((he.const_mul (2*b)).div
    ((hasDerivAt_const t (1:ℝ)).add he) hd.ne')
  apply h.congr_deriv
  simp only [id_eq,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
  field_simp
  <;> ring

theorem bubbleExpPower_second (a b t:ℝ):
    deriv (deriv (bubbleExpPower a b)) t=bubbleExpPower a b t*
      (bubbleLogSlope a b t^2+4*b*Real.exp (2*t)/(1+Real.exp (2*t))^2):=by
  have hfirst:deriv (bubbleExpPower a b)=fun s=>bubbleExpPower a b s*bubbleLogSlope a b s:=
    funext fun s=>(bubbleExpPower_hasDerivAt a b s).deriv
  rw [hfirst]
  have h:=(bubbleExpPower_hasDerivAt a b t).mul (bubbleLogSlope_hasDerivAt a b t)
  apply HasDerivAt.deriv
  convert h using 1 <;> first | rfl | (funext s; dsimp; ring) | ring

def bubbleLowTranslation (t:ℝ):ℝ:=bubbleExpPower (3/2) (-3/2) t

def bubbleLowRadial (t:ℝ):ℝ:=bubbleExpPower (1/2) (-3/2) t*(1-Real.exp (2*t))

theorem bubbleLowTranslation_smooth:ContDiff ℝ ∞ bubbleLowTranslation:=bubbleExpPower_smooth _ _

theorem bubbleLowRadial_smooth:ContDiff ℝ ∞ bubbleLowRadial:=
  (bubbleExpPower_smooth _ _).mul (contDiff_const.sub (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))

theorem bubbleLowTranslation_equation (t:ℝ):
    deriv (deriv bubbleLowTranslation) t-(1/4+2)*bubbleLowTranslation t+
      (15/4)*fullBubbleDensity t*bubbleLowTranslation t=0:=by
  unfold bubbleLowTranslation
  rw [bubbleExpPower_second]
  unfold bubbleLogSlope fullBubbleDensity
  have hd:1+Real.exp (2*t)≠0:=ne_of_gt (by positivity)
  field_simp
  <;> ring

theorem bubbleLowRadial_hasDerivAt (t:ℝ):
    HasDerivAt bubbleLowRadial
      (bubbleExpPower (1/2) (-3/2) t*bubbleLogSlope (1/2) (-3/2) t*(1-Real.exp (2*t))-
        2*bubbleExpPower (1/2) (-3/2) t*Real.exp (2*t)) t:=by
  have h:=(bubbleExpPower_hasDerivAt (1/2) (-3/2) t).mul
    ((hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).const_mul 2).exp))
  apply h.congr_deriv
  simp only [id_eq,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
  ring

theorem bubbleLowRadial_second (t:ℝ):
    deriv (deriv bubbleLowRadial) t=
      bubbleExpPower (1/2) (-3/2) t*
        (bubbleLogSlope (1/2) (-3/2) t^2-6*Real.exp (2*t)/(1+Real.exp (2*t))^2)*(1-Real.exp (2*t))-
      4*bubbleExpPower (1/2) (-3/2) t*bubbleLogSlope (1/2) (-3/2) t*Real.exp (2*t)-
      4*bubbleExpPower (1/2) (-3/2) t*Real.exp (2*t):=by
  have hfirst:deriv bubbleLowRadial=fun s=>
      bubbleExpPower (1/2) (-3/2) s*bubbleLogSlope (1/2) (-3/2) s*(1-Real.exp (2*s))-
        2*bubbleExpPower (1/2) (-3/2) s*Real.exp (2*s):=funext fun s=>(bubbleLowRadial_hasDerivAt s).deriv
  rw [hfirst]
  have hp:=bubbleExpPower_hasDerivAt (1/2) (-3/2) t
  have hl:=bubbleLogSlope_hasDerivAt (1/2) (-3/2) t
  have he:=((hasDerivAt_id t).const_mul 2).exp
  have h:=((hp.mul hl).mul ((hasDerivAt_const t (1:ℝ)).sub he)).sub
    ((hp.const_mul 2).mul he)
  apply HasDerivAt.deriv
  convert h using 1 <;> first | rfl | (funext s; dsimp; ring) | (simp only [id_eq,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)

theorem bubbleLowRadial_equation (t:ℝ):
    deriv (deriv bubbleLowRadial) t-(1/4)*bubbleLowRadial t+
      (15/4)*fullBubbleDensity t*bubbleLowRadial t=0:=by
  rw [bubbleLowRadial_second]
  unfold bubbleLowRadial bubbleLogSlope fullBubbleDensity
  have hd:1+Real.exp (2*t)≠0:=ne_of_gt (by positivity)
  field_simp
  <;> ring

theorem bubbleLowTranslation_ne_zero (t:ℝ):bubbleLowTranslation t≠0:=
  (bubbleExpPower_pos _ _ _).ne'

theorem bubbleLowRadial_ne_zero_after_peak {t:ℝ} (ht:0<t):bubbleLowRadial t≠0:=by
  apply mul_ne_zero (bubbleExpPower_pos _ _ _).ne'
  have he:1<Real.exp (2*t):=Real.one_lt_exp_iff.mpr (by linarith)
  linarith

#print axioms bubbleExpPower_hasDerivAt
#print axioms bubbleExpPower_second
#print axioms bubbleLowTranslation_equation
#print axioms bubbleLowRadial_equation
#print axioms bubbleLowTranslation_ne_zero
#print axioms bubbleLowRadial_ne_zero_after_peak
end Yamabe3.Analysis.Delaunay
