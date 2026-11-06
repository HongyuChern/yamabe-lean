import Yamabe3.Analysis.NativePrincipalErrorContinuity

/-! Actual divergence linearity on the C2 representatives retained by
H4 graphs. No linearity is asserted for arbitrary nonsmooth totalizations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem principalSource_add_C2On {a : E → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) {W : Set E} (hW : IsOpen W)
    {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u W) (hv : ContDiffOn ℝ 2 v W)
    {x : E} (hx : x ∈ W) :
    principalSource a (fun y => u y+v y) x = principalSource a u x+principalSource a v x := by
  have hp (j : Fin 3) : partialDeriv j (fun y => u y+v y) =ᶠ[𝓝 x]
      fun y => partialDeriv j u y+partialDeriv j v y := by
    filter_upwards [hW.mem_nhds hx] with y hy
    unfold partialDeriv
    rw [fderiv_fun_add ((hu.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num))
      ((hv.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num))]
    rfl
  have hflux (i : Fin 3) : matrixFlux a (fun j => partialDeriv j (fun y => u y+v y)) i =ᶠ[𝓝 x]
      fun y => matrixFlux a (fun j => partialDeriv j u) i y+matrixFlux a (fun j => partialDeriv j v) i y := by
    filter_upwards [eventually_all.mpr hp] with y hy
    simp only [matrixFlux,hy,mul_add,Finset.sum_add_distrib]
  have hdiff (u : E → ℝ) (hu : ContDiffOn ℝ 2 u W) (i : Fin 3) :
      DifferentiableAt ℝ (matrixFlux a (fun j => partialDeriv j u) i) x := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 3, a y i j * partialDeriv j u y) x
    apply DifferentiableAt.fun_sum
    intro j _
    exact ((ha i j).differentiable (by simp) x).mul
      ((((hu.contDiffAt (hW.mem_nhds hx)).fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).clm_apply
        contDiffAt_const).differentiableAt (by norm_num))
  have hpart (i : Fin 3) : partialDeriv i (matrixFlux a (fun j => partialDeriv j (fun y => u y+v y)) i) x =
      partialDeriv i (matrixFlux a (fun j => partialDeriv j u) i) x+
        partialDeriv i (matrixFlux a (fun j => partialDeriv j v) i) x := by
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1))
      ((hflux i).fderiv_eq (𝕜 := ℝ) |>.trans (fderiv_fun_add (hdiff u hu i) (hdiff v hv i)))
    exact hh
  unfold principalSource
  simp only [hpart,Finset.sum_add_distrib,neg_add_rev]
  ring

theorem principalSource_const_mul (a : E → Matrix (Fin 3) (Fin 3) ℝ)
    (u : E → ℝ) (c : ℝ) (x : E) :
    principalSource a (fun y => c*u y) x = c*principalSource a u x := by
  simpa only [one_smul,sub_zero,one_pow,mul_one] using principalSource_scaled_centered a u 1 c 0 x

theorem nativeNormalizedPrincipalError_graph_add (g : RiemannianMetric 3 E) (ε : ℝ)
    (v w : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) :
    nativeNormalizedPrincipalError g ε (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (v+w))) x =
      nativeNormalizedPrincipalError g ε (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x+
        nativeNormalizedPrincipalError g ε (halfEndEntranceExtension (halfEndPhysicalH4GraphValue w)) x := by
  have hx : (x:E) ∈ ball (0:E) 4 \ {(0:E)} :=
    ⟨by simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt x.2.2 (by norm_num : (3:ℝ)<4),x.2.1⟩
  have he : halfEndEntranceExtension (halfEndPhysicalH4GraphValue (v+w)) =
      fun y => halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) y+
        halfEndEntranceExtension (halfEndPhysicalH4GraphValue w) y := by
    funext y
    rw [map_add,halfEndEntranceExtension_add]
  unfold nativeNormalizedPrincipalError nativePrincipalError
  rw [he,principalSource_add_C2On (a := fun y => nativeDivergenceMatrix g (ε • y)-1) (contDiff_nativeScaledPrincipalError g ε)
    (isOpen_ball.sdiff isClosed_singleton) (halfEndPhysicalH4Graph_contDiffOn_two v)
    (halfEndPhysicalH4Graph_contDiffOn_two w) hx]
  ring

theorem nativeNormalizedPrincipalError_graph_smul (g : RiemannianMetric 3 E) (ε c : ℝ)
    (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) :
    nativeNormalizedPrincipalError g ε (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (c • v))) x =
      c*nativeNormalizedPrincipalError g ε (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x := by
  have he : halfEndEntranceExtension (halfEndPhysicalH4GraphValue (c • v)) =
      fun y => c*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) y := by
    funext y
    rw [map_smul,halfEndEntranceExtension_smul]
  unfold nativeNormalizedPrincipalError nativePrincipalError
  rw [he,principalSource_const_mul]
  ring

#print axioms principalSource_add_C2On
#print axioms nativeNormalizedPrincipalError_graph_add
#print axioms nativeNormalizedPrincipalError_graph_smul
end Yamabe3.Analysis.UniformElliptic
