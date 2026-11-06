import Yamabe3.Analysis.FutureL2Continuity
import Yamabe3.Analysis.BanachFutureLinearity

/-! Canonical bounded continuous future tails and actual entrance maps.
The maps are constructed from the L2 source, not chosen as extra inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def futureL2SmoothCurve (k : ℝ) (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) : ℝ →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (futureL2Convolution k F)
    (futureL2Convolution_continuous hk F (Lp.memLp F))
    ((eLpNorm (futureL2Kernel k) 2).toReal*‖F‖) (by
      intro t
      exact futureL2Convolution_uniform_norm hk F t)

theorem futureL2SmoothCurve_norm {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖futureL2SmoothCurve k hk F‖≤(eLpNorm (futureL2Kernel k) 2).toReal*‖F‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (futureL2Convolution_uniform_norm hk F)

theorem futureL2SmoothCurve_add {k : ℝ} (hk : 0<k) (F G : Lp H 2 (volume : Measure ℝ)) :
    futureL2SmoothCurve k hk (F+G)=futureL2SmoothCurve k hk F+futureL2SmoothCurve k hk G := by
  apply BoundedContinuousFunction.ext
  intro t
  change futureL2Convolution k ⇑(F+G) t=futureL2Convolution k F t+futureL2Convolution k G t
  rw [futureL2Convolution_congr_ae k (Lp.coeFn_add F G)]
  unfold futureL2Convolution
  simp only [Pi.add_apply,smul_add]
  exact integral_add (futureL2Convolution_everywhere_integrable hk F (Lp.memLp F) t)
    (futureL2Convolution_everywhere_integrable hk G (Lp.memLp G) t)

theorem futureL2SmoothCurve_smul {k : ℝ} (hk : 0<k) (c : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    futureL2SmoothCurve k hk (c • F)=c • futureL2SmoothCurve k hk F := by
  apply BoundedContinuousFunction.ext
  intro t
  change futureL2Convolution k ⇑(c • F) t=c • futureL2Convolution k F t
  rw [futureL2Convolution_congr_ae k (Lp.coeFn_smul c F)]
  unfold futureL2Convolution
  simp only [Pi.smul_apply]
  simp_rw [smul_comm (futureL2Kernel k (t-_)) c]
  exact integral_smul c _

def futureL2SmoothingCLM (k : ℝ) (hk : 0<k) : Lp H 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ H) :=
  ({toFun := futureL2SmoothCurve k hk
    map_add' := futureL2SmoothCurve_add hk
    map_smul' := futureL2SmoothCurve_smul hk} :
      Lp H 2 (volume : Measure ℝ) →ₗ[ℝ] (ℝ →ᵇ H)).mkContinuous
    (eLpNorm (futureL2Kernel k) 2).toReal (by
      intro F
      exact futureL2SmoothCurve_norm hk F)

theorem futureL2Smoothing_norm {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖futureL2SmoothingCLM k hk F‖ ≤ (eLpNorm (futureL2Kernel k) 2).toReal*‖F‖ := by
  exact futureL2SmoothCurve_norm hk F

theorem futureL2Smoothing_ae {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    (futureL2SmoothingCLM k hk F : ℝ → H)=ᵐ[volume](futureL2ResolventCLM k hk F : ℝ → H) :=
  (futureL2Resolvent_coe_ae hk F).symm

def boundedFutureResolventCLM (k : ℝ) (hk : 0<k) : (ℝ →ᵇ H) →L[ℝ] (ℝ →ᵇ H) :=
  ({toFun := banachFutureResolvent k hk
    map_add' := banachFutureResolvent_add hk
    map_smul' := banachFutureResolvent_smul hk} :
      (ℝ →ᵇ H) →ₗ[ℝ] (ℝ →ᵇ H)).mkContinuous (1/k)
    (fun F => by
      change ‖banachFutureResolvent k hk F‖ ≤ (1/k)*‖F‖
      simpa only [div_eq_mul_inv,one_mul,mul_comm ‖F‖] using banachFutureResolvent_norm_le hk F)

def doubleFutureL2SmoothingCLM (k : ℝ) (hk : 0<k) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ H) :=
  (boundedFutureResolventCLM k hk).comp (futureL2SmoothingCLM k hk)

theorem doubleFutureL2Smoothing_ae {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    (doubleFutureL2SmoothingCLM k hk F : ℝ → H)=ᵐ[volume](doubleFutureL2CLM k hk F : ℝ → H) := by
  have h := futureL2Resolvent_coe_ae hk (futureL2ResolventCLM k hk F)
  rw [futureL2Convolution_congr_ae k (futureL2Smoothing_ae hk F).symm] at h
  filter_upwards [h] with t ht
  exact (futureL2Convolution_eq_tail k (futureL2SmoothingCLM k hk F) t).symm.trans ht.symm

theorem doubleFutureL2Smoothing_hasDerivAt {k : ℝ} (hk : 0<k)
    (F : Lp H 2 (volume : Measure ℝ)) (t : ℝ) :
    HasDerivAt (fun s => doubleFutureL2SmoothingCLM k hk F s)
      (k • doubleFutureL2SmoothingCLM k hk F t-futureL2SmoothingCLM k hk F t) t :=
  banachFutureTail_hasDerivAt hk (futureL2SmoothingCLM k hk F) t

theorem doubleFutureL2Smoothing_norm {k : ℝ} (hk : 0<k) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖doubleFutureL2SmoothingCLM k hk F‖≤((eLpNorm (futureL2Kernel k) 2).toReal/k)*‖F‖ := by
  apply (banachFutureResolvent_norm_le hk (futureL2SmoothingCLM k hk F)).trans
  exact (div_le_div_of_nonneg_right (futureL2SmoothCurve_norm hk F) hk.le).trans_eq (by ring)

#print axioms futureL2SmoothCurve_norm
#print axioms futureL2SmoothCurve_add
#print axioms futureL2SmoothCurve_smul
#print axioms futureL2Smoothing_norm
#print axioms futureL2Smoothing_ae
#print axioms doubleFutureL2Smoothing_ae
#print axioms doubleFutureL2Smoothing_hasDerivAt
#print axioms doubleFutureL2Smoothing_norm
end Yamabe3.Analysis.Delaunay
