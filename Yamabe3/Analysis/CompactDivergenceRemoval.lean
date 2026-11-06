import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! A continuous compact vector field has zero total divergence even
when its classical derivative is undefined on a countable set, provided
its actual divergence is integrable. This uses the proved countable-
exception divergence theorem, not a formal deletion of a point mass. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "P" => (Fin 3→ℝ)

theorem integral_compact_divergence_off_countable
    {f:P→P} (hf:Continuous f) (hc:HasCompactSupport f)
    {s:Set P} (hs:s.Countable) (hd:∀x∉s,DifferentiableAt ℝ f x)
    (hi:Integrable (fun x:P=>∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i)) :
    (∫x:P,∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i)=0 := by
  obtain ⟨R,hR,hbound⟩:=hc.isCompact.isBounded.exists_pos_norm_lt
  let a:P:=fun _=>-R
  let b:P:=fun _=>R
  have hab:a ≤ b:=fun i=>by dsimp [a,b]; linarith
  have hsup:tsupport f⊆Icc a b := by
    intro x hx
    have hn:=hbound x hx
    constructor
    · intro i
      have hxnorm:=norm_le_pi_norm x i
      have hxi:|x i|<R:= (show |x i| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using hxnorm).trans_lt hn
      exact (abs_lt.mp hxi).1.le
    · intro i
      have hxnorm:=norm_le_pi_norm x i
      have hxi:|x i|<R:= (show |x i| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using hxnorm).trans_lt hn
      exact (abs_lt.mp hxi).2.le
  have hzero(x:P)(hx:x∉Icc a b): (∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i)=0 := by
    have hxs:x∉tsupport f:=fun ht=>hx (hsup ht)
    have he:f=ᶠ[𝓝 x] (fun _=>0) := notMem_tsupport_iff_eventuallyEq.mp hxs
    rw [he.fderiv_eq]
    simp
  have hface(i:Fin 3)(t:ℝ)(ht:|t|=R)(x:Fin 2→ℝ):f (i.insertNth t x)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hn:=hbound _ hx
    have hlo:=norm_le_pi_norm (i.insertNth t x:P) i
    simp only [Fin.insertNth_apply_same,Real.norm_eq_abs,ht] at hlo
    linarith
  have hdiv:=integral_divergence_of_hasFDerivAt_off_countable (n:=2) a b hab f
    (fderiv ℝ f) s hs hf.continuousOn (fun x hx=>(hd x hx.2).hasFDerivAt) hi.integrableOn
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero,hdiv]
  apply Finset.sum_eq_zero
  intro i _
  have hfront(x:Fin 2→ℝ):f (i.insertNth (b i) x)=0:=hface i R (abs_of_pos hR) x
  have hback(x:Fin 2→ℝ):f (i.insertNth (a i) x)=0:=hface i (-R) (by rw [abs_neg,abs_of_pos hR]) x
  simp only [hfront,hback,Pi.zero_apply,integral_zero,sub_self]

#print axioms integral_compact_divergence_off_countable
end Yamabe3.Analysis.UniformElliptic
