import Yamabe3.Analysis.Cylinder.NativeSphereRestriction

/-! The actual round-sphere Laplacian consumes the same ambient two-jet,
with all radial correction terms retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

theorem sphere_laplacian_bound_of_ambient_two_jets {f:E→ℝ} (θ:S)
    (hf:ContDiffAt ℝ ∞ f (θ:E)) {A:ℝ} (hA:0≤A)
    (hj:∀j≤2,‖iteratedFDeriv ℝ j f (θ:E)‖≤A) :
    |sphereD.laplacian (fun η:S=>f η) θ|≤6*A := by
  have hθ:‖(θ:E)‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using θ.property
  have hH:∀v:E,‖v‖=1 → |fderiv ℝ (fderiv ℝ f) (θ:E) v v|≤A:=by
    intro v hv
    have he:iteratedFDeriv ℝ 2 f (θ:E) (fun _:Fin 2=>v)=fderiv ℝ (fderiv ℝ f) (θ:E) v v:=by
      rw [iteratedFDeriv_two_apply]
    have hb:=(iteratedFDeriv ℝ 2 f (θ:E)).le_opNorm (fun _:Fin 2=>v)
    rw [he] at hb
    have hc:‖fderiv ℝ (fderiv ℝ f) (θ:E) v v‖≤‖iteratedFDeriv ℝ 2 f (θ:E)‖:=by
      simpa only [hv,Finset.prod_const_one,mul_one] using hb
    exact (by simpa only [Real.norm_eq_abs] using hc.trans (hj 2 (le_refl 2)))
  have hL:|euclideanD.laplacian f (θ:E)|≤3*A:=by
    rw [laplacian_euclidean_in_orthonormalBasis hf (EuclideanSpace.basisFun (Fin 3) ℝ)]
    calc
      _ ≤ ∑i:Fin 3,|fderiv ℝ (fderiv ℝ f) (θ:E)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)|:=Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_:Fin 3,A:=Finset.sum_le_sum (fun i _=>hH _ ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i))
      _ = _:=by simp
  have hD:|fderiv ℝ f (θ:E) (θ:E)|≤A:=by
    have hh:=(fderiv ℝ f (θ:E)).le_opNorm (θ:E)
    rw [hθ,mul_one] at hh
    have hn:‖fderiv ℝ f (θ:E)‖≤A:=by simpa only [norm_iteratedFDeriv_one] using hj 1 (by norm_num)
    simpa only [Real.norm_eq_abs] using hh.trans hn
  rw [laplacian_restriction θ hf]
  calc
    _ ≤ |euclideanD.laplacian f (θ:E)-fderiv ℝ (fderiv ℝ f) (θ:E) (θ:E) (θ:E)|+
        |2*fderiv ℝ f (θ:E) (θ:E)|:=abs_sub _ _
    _ ≤ (|euclideanD.laplacian f (θ:E)|+|fderiv ℝ (fderiv ℝ f) (θ:E) (θ:E) (θ:E)|)+
        2*|fderiv ℝ f (θ:E) (θ:E)|:=by rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<2)];exact add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ (3*A+A)+2*A:=add_le_add (add_le_add hL (hH _ hθ)) (mul_le_mul_of_nonneg_left hD (by norm_num))
    _ = _:=by ring

#print axioms sphere_laplacian_bound_of_ambient_two_jets
end Yamabe3.Analysis.SpherePolar
