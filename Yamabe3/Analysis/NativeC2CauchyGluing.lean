import Yamabe3.Analysis.NativeSphereGreenC2

/-! The same-metric C2 second Green identity and exact weak splice.
This is an interface theorem for actual C2 fields and actual matching
Cauchy data, not a claim that matching fields have already been produced. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
namespace Yamabe3.Analysis.EuclideanSphereTrace
open SphereBoundaryLayer GreenParametrix GreenMass.NativeGaussSphereArea
variable (g:RiemannianMetric 3 E)
  (hGauss:∀x v:E,g.inner x x v=inner ℝ x v)
  {r:ℝ} (hr:0<r)
local notation "B" => closedBall (0:E) r

include hGauss hr in
private theorem exterior_green_compl_C2 {f ψ:E→ℝ}
    (hf:ContDiff ℝ 2 f) (hψ:ContDiff ℝ 2 ψ) (hc:HasCompactSupport ψ):
    (∫x in Bᶜ,ψ x*g.leviCivitaData.laplacian f x+g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient f x) ∂g.volumeMeasure)=
      -(∫θ:S,ψ (r • (θ:E))*fderiv ℝ f (r • (θ:E)) (θ:E) ∂(gaussRadiusMetric g r hr.ne').volumeMeasure):=by
  have heq:Bᶜ={y:E|r<‖y‖}:=by ext x; simp only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le,mem_setOf_eq]
  rw [heq]
  exact integral_native_exterior_sphere_green_C2 g hGauss hr hf hψ hc

private theorem integrable_pair_C2 {u v:E→ℝ} (hu:ContDiff ℝ 2 u)
    (hv:ContDiff ℝ 2 v) (hc:HasCompactSupport u):
    Integrable (fun x=>u x*g.leviCivitaData.laplacian v x) g.volumeMeasure:=
  (hu.continuous.mul (continuous_native_laplacian_C2 g hv)).integrable_of_hasCompactSupport hc.mul_right

include hGauss hr in
theorem integral_native_exterior_second_green_C2 {f ψ:E→ℝ}
    (hf:ContDiff ℝ 2 f) (hψ:ContDiff ℝ 2 ψ)
    (hfc:HasCompactSupport f) (hψc:HasCompactSupport ψ):
    (∫x in Bᶜ,f x*(-8*g.leviCivitaData.laplacian ψ x) ∂g.volumeMeasure)-
      (∫x in Bᶜ,(-8*g.leviCivitaData.laplacian f x)*ψ x ∂g.volumeMeasure)=
      8*((∫θ:S,f (r • (θ:E))*fderiv ℝ ψ (r • (θ:E)) (θ:E) ∂(gaussRadiusMetric g r hr.ne').volumeMeasure)-
        (∫θ:S,ψ (r • (θ:E))*fderiv ℝ f (r • (θ:E)) (θ:E) ∂(gaussRadiusMetric g r hr.ne').volumeMeasure)):=by
  have h1:=exterior_green_compl_C2 g hGauss hr hψ hf hfc
  have h2:=exterior_green_compl_C2 g hGauss hr hf hψ hψc
  rw [integral_add (integrable_pair_C2 g hf hψ hfc).integrableOn
    (integrable_native_inner_gradient_C2 g hf hψ hfc).integrableOn] at h1
  rw [integral_add (integrable_pair_C2 g hψ hf hψc).integrableOn
    (integrable_native_inner_gradient_C2 g hψ hf hψc).integrableOn] at h2
  have hs:(∫x in Bᶜ,g.inner x (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient ψ x) ∂g.volumeMeasure)=
      ∫x in Bᶜ,g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient f x) ∂g.volumeMeasure:=by
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>g.symm x _ _
  rw [hs] at h1
  have hl:(∫x in Bᶜ,f x*(-8*g.leviCivitaData.laplacian ψ x) ∂g.volumeMeasure)=
      -8*(∫x in Bᶜ,f x*g.leviCivitaData.laplacian ψ x ∂g.volumeMeasure):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by ring
  have hright:(∫x in Bᶜ,(-8*g.leviCivitaData.laplacian f x)*ψ x ∂g.volumeMeasure)=
      -8*(∫x in Bᶜ,ψ x*g.leviCivitaData.laplacian f x ∂g.volumeMeasure):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by ring
  rw [hl,hright]
  linarith only [h1,h2]

private theorem global_comm_C2 {f ψ:E→ℝ}
    (hf:ContDiff ℝ 2 f) (hψ:ContDiff ℝ 2 ψ)
    (hfc:HasCompactSupport f) (hψc:HasCompactSupport ψ):
    (∫x,f x*(-8*g.leviCivitaData.laplacian ψ x) ∂g.volumeMeasure)=
      ∫x,(-8*g.leviCivitaData.laplacian f x)*ψ x ∂g.volumeMeasure:=by
  have h1:=integral_native_mul_laplacian_C2 g hf hψ hfc
  have h2:=integral_native_mul_laplacian_C2 g hψ hf hψc
  have hs:(∫x,g.inner x (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient ψ x) ∂g.volumeMeasure)=
      ∫x,g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient f x) ∂g.volumeMeasure:=by
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>g.symm x _ _
  rw [hs] at h1
  calc
    _ = -8*(∫x,f x*g.leviCivitaData.laplacian ψ x ∂g.volumeMeasure):=by
      rw [←integral_const_mul]; apply integral_congr_ae
      exact Eventually.of_forall fun x=>by ring
    _ = -8*(∫x,ψ x*g.leviCivitaData.laplacian f x ∂g.volumeMeasure):=by rw [h1,h2]
    _ = _:=by
      rw [←integral_const_mul]; apply integral_congr_ae
      exact Eventually.of_forall fun x=>by ring

include hGauss hr in
theorem native_c2_cauchy_gluing_no_interface_source
    (c : E → ℝ) (hc : Continuous c) {f h : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hh : ContDiff ℝ 2 h)
    (hfc:HasCompactSupport f) (hhc:HasCompactSupport h)
    (hvalue : ∀ θ : S, f ((r • (θ : E))) = h ((r • (θ : E))))
    (hnormal : ∀ θ : S,
      fderiv ℝ f (r • (θ : E)) (θ : E) =
        fderiv ℝ h (r • (θ : E)) (θ : E))
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc:HasCompactSupport φ) :
    (∫ x, (closedBall (0 : E) r).piecewise f h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)
        ∂g.volumeMeasure) =
      ∫ x, (closedBall (0 : E) r).piecewise (fun y => -8 * g.leviCivitaData.laplacian f y + c y * f y)
        (fun y => -8 * g.leviCivitaData.laplacian h y + c y * h y) x * φ x ∂g.volumeMeasure := by
  classical
  have hB : MeasurableSet B :=
    isClosed_closedBall.measurableSet
  have hint (v : E → ℝ) (hv : ContDiff ℝ 2 v) :
      Integrable (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x)) g.volumeMeasure :=
    (hv.continuous.mul ((continuous_native_laplacian_C2 g hφ).const_mul (-8))).integrable_of_hasCompactSupport
      (g.leviCivitaData.hasCompactSupport_laplacian hφc).mul_left.mul_left
  have hsrc (v : E → ℝ) (hv : ContDiff ℝ 2 v) :
      Integrable (fun x => (-8 * g.leviCivitaData.laplacian v x) * φ x) g.volumeMeasure :=
    (((continuous_native_laplacian_C2 g hv).const_mul (-8)).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left
  have hpot (v : E → ℝ) (hv : ContDiff ℝ 2 v) :
      Integrable (fun x => c x * v x * φ x) g.volumeMeasure :=
    ((hc.mul hv.continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left
  have hsplitL (v : E → ℝ) (hv : ContDiff ℝ 2 v) (A : Set E) :
      (∫ x in A, v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x) ∂g.volumeMeasure) =
        (∫ x in A, v x * (-8 * g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure) +
          ∫ x in A, c x * v x * φ x ∂g.volumeMeasure := by
    rw [← integral_add (hint v hv).integrableOn (hpot v hv).integrableOn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hsplitR (v : E → ℝ) (hv : ContDiff ℝ 2 v) (A : Set E) :
      (∫ x in A, (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x ∂g.volumeMeasure) =
        (∫ x in A, (-8 * g.leviCivitaData.laplacian v x) * φ x ∂g.volumeMeasure) +
          ∫ x in A, c x * v x * φ x ∂g.volumeMeasure := by
    rw [← integral_add (hsrc v hv).integrableOn (hpot v hv).integrableOn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hleft : (fun x => (closedBall (0 : E) r).piecewise f h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) =
      (closedBall (0 : E) r).piecewise (fun x => f x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x))
        (fun x => h x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hright : (fun x => (closedBall (0 : E) r).piecewise
      (fun y => -8 * g.leviCivitaData.laplacian f y + c y * f y)
      (fun y => -8 * g.leviCivitaData.laplacian h y + c y * h y) x * φ x) =
      (closedBall (0 : E) r).piecewise (fun x => (-8 * g.leviCivitaData.laplacian f x + c x * f x) * φ x)
        (fun x => (-8 * g.leviCivitaData.laplacian h x + c x * h x) * φ x) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hiL (v : E → ℝ) (hv : ContDiff ℝ 2 v) :
      Integrable (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) g.volumeMeasure := by
    have heq : (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x + c x * φ x)) =
        (fun x => v x * (-8 * g.leviCivitaData.laplacian φ x) + c x * v x * φ x) := by
      funext x; ring
    rw [heq]
    exact (hint v hv).add (hpot v hv)
  have hiR (v : E → ℝ) (hv : ContDiff ℝ 2 v) :
      Integrable (fun x => (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x) g.volumeMeasure := by
    have heq : (fun x => (-8 * g.leviCivitaData.laplacian v x + c x * v x) * φ x) =
        (fun x => (-8 * g.leviCivitaData.laplacian v x) * φ x + c x * v x * φ x) := by
      funext x; ring
    rw [heq]
    exact (hsrc v hv).add (hpot v hv)
  rw [hleft, hright,
    integral_piecewise hB (hiL f hf).integrableOn (hiL h hh).integrableOn,
    integral_piecewise hB (hiR f hf).integrableOn (hiR h hh).integrableOn,
    hsplitL f hf B, hsplitL h hh Bᶜ, hsplitR f hf B, hsplitR h hh Bᶜ]
  have hglobal := global_comm_C2 g hf hφ hfc hφc
  have hdecompL := integral_add_compl hB (hint f hf)
  have hdecompR := integral_add_compl hB (hsrc f hf)
  have h1:=integral_native_exterior_second_green_C2 g hGauss hr hf hφ hfc hφc
  have h2:=integral_native_exterior_second_green_C2 g hGauss hr hh hφ hhc hφc
  have hexterior:(∫x in Bᶜ,f x*(-8*g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure)-
      (∫x in Bᶜ,(-8*g.leviCivitaData.laplacian f x)*φ x ∂g.volumeMeasure)=
      (∫x in Bᶜ,h x*(-8*g.leviCivitaData.laplacian φ x) ∂g.volumeMeasure)-
      (∫x in Bᶜ,(-8*g.leviCivitaData.laplacian h x)*φ x ∂g.volumeMeasure):=by
    rw [h1,h2]
    simp_rw [hvalue,hnormal]
  linarith only [hglobal, hdecompL, hdecompR, hexterior]


#print axioms integral_native_exterior_second_green_C2
#print axioms native_c2_cauchy_gluing_no_interface_source
end Yamabe3.Analysis.EuclideanSphereTrace
