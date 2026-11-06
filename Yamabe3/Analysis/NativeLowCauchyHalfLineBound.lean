import Yamabe3.Analysis.NativeLowCauchyBoundedCollar
import Yamabe3.Analysis.BubbleLowPastSolver

/-! Bounds on the actual compensated low Cauchy solutions, uniform in
all times below a fixed endpoint. The constants precede both entrance
data. No whole-line square integrability is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem exists_continuous_atBot_halfLine_bound {f : ℝ→ℝ} (hf : Continuous f)
    (hl : Tendsto f atBot (𝓝 0)) (c : ℝ) :
    ∃M : ℝ,0≤M ∧ ∀t≤c,‖f t‖≤M := by
  have he : ∀ᶠ t in atBot,‖f t‖<1 := by
    have h := hl.norm.eventually (gt_mem_nhds (by norm_num : ‖(0:ℝ)‖<1))
    exact h
  obtain ⟨a,ha⟩ := (eventually_atBot).mp he
  obtain ⟨M,hM⟩ := (isCompact_Icc.bddAbove_image (hf.norm.continuousOn) :
    BddAbove ((fun t => ‖f t‖) '' Icc a c))
  refine ⟨max 1 M,le_trans (by norm_num) (le_max_left _ _),fun t ht => ?_⟩
  by_cases hta : t≤a
  · exact (ha t hta).le.trans (le_max_left _ _)
  · exact (hM (mem_image_of_mem _ ⟨le_of_not_ge hta,ht⟩)).trans (le_max_right _ _)

private theorem unit_bound (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {τ : ℝ} (ht : 0<τ) (d n c : ℝ) :
    let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
    ∃M : ℝ,0≤M ∧ ∀t≤c,‖q t‖≤M ∧ ‖deriv q t‖≤M ∧ ‖deriv (deriv q) t‖≤M := by
  let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
  have h := bubbleLowZeroCauchyLinear_spec i hi ht d n
  change ContDiff ℝ 2 q ∧ _ at h
  obtain ⟨A,hA,ha⟩ := exists_continuous_atBot_halfLine_bound h.1.continuous h.2.2.2.2.1 c
  have hd : Continuous (deriv q) := h.1.continuous_deriv (by norm_num)
  obtain ⟨B,hB,hb⟩ := exists_continuous_atBot_halfLine_bound hd h.2.2.2.2.2 c
  obtain ⟨D,hD⟩ := (bubbleCompensation_smooth_compact i).2.exists_bound_of_continuous
    (bubbleCompensation_smooth_compact i).1.continuous
  let L := ‖bubbleLowCauchyCompensation i τ d n 0‖
  let M := A+B+(7/2)*A+L*max 0 D
  have hM : 0≤M := by dsimp [M,L]; positivity
  refine ⟨M,hM,fun t hc => ⟨?_,?_,?_⟩⟩
  · exact (ha t hc).trans (by have hh : 0≤L*max 0 D := mul_nonneg (norm_nonneg _) (le_max_left _ _); dsimp [M]; linarith)
  · exact (hb t hc).trans (by have hh : 0≤L*max 0 D := mul_nonneg (norm_nonneg _) (le_max_left _ _); dsimp [M]; linarith)
  · have he : deriv (deriv q) t=bubbleLowCoefficient i t*q t-
        bubbleLowCauchyCompensation i τ d n 0*bubbleCompensation i t := by linarith [h.2.1 t]
    rw [he]
    have hc0 : ‖bubbleLowCoefficient i t‖≤7/2 := by
      simpa only [Real.norm_eq_abs] using bubbleLowCoefficient_bound i hi t
    have hd0 : ‖bubbleCompensation i t‖≤ max 0 D := (hD t).trans (le_max_right _ _)
    calc
      _ ≤ ‖bubbleLowCoefficient i t*q t‖+‖bubbleLowCauchyCompensation i τ d n 0*bubbleCompensation i t‖ := norm_sub_le _ _
      _ ≤ (7/2)*A+L*max 0 D := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hc0 (ha t hc) (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hd0 (norm_nonneg _))
      _ ≤ M := by dsimp [M]; linarith

theorem bubbleLowZeroCauchyLinear_halfLine_bound (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {τ : ℝ} (ht : 0<τ) (c : ℝ) :
    ∃M : ℝ,0≤M ∧ ∀d n t : ℝ,t≤c →
      let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
      ‖q t‖≤M*max ‖d‖ ‖n‖ ∧ ‖deriv q t‖≤M*max ‖d‖ ‖n‖ ∧
      ‖deriv (deriv q) t‖≤M*max ‖d‖ ‖n‖ := by
  let a := bubbleLowZeroCauchyLinear i hi ht (1,0)
  let b := bubbleLowZeroCauchyLinear i hi ht (0,1)
  have ha := (bubbleLowZeroCauchyLinear_spec i hi ht 1 0).1
  have hb := (bubbleLowZeroCauchyLinear_spec i hi ht 0 1).1
  obtain ⟨A,hA,hAb⟩ := unit_bound i hi ht 1 0 c
  obtain ⟨B,hB,hBb⟩ := unit_bound i hi ht 0 1 c
  refine ⟨A+B,add_nonneg hA hB,fun d n t hc => ?_⟩
  have he : bubbleLowZeroCauchyLinear i hi ht (d,n)=fun t => d*a t+n*b t := by
    have hv : (d,n)=d • ((1,0):ℝ×ℝ)+n • ((0,1):ℝ×ℝ) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]; rfl
  have hd : deriv (fun t => d*a t+n*b t)=fun t => d*deriv a t+n*deriv b t := by
    funext t
    exact (((ha.differentiable (by norm_num) t).hasDerivAt.const_mul d).add
      ((hb.differentiable (by norm_num) t).hasDerivAt.const_mul n)).deriv
  have hdd : deriv (deriv (fun t => d*a t+n*b t))=fun t => d*deriv (deriv a) t+n*deriv (deriv b) t := by
    rw [hd];funext t
    exact (((ha.differentiable_deriv_two t).hasDerivAt.const_mul d).add
      ((hb.differentiable_deriv_two t).hasDerivAt.const_mul n)).deriv
  have hbound {x y : ℝ} (hx : ‖x‖≤A) (hy : ‖y‖≤B) :
      ‖d*x+n*y‖≤(A+B)*max ‖d‖ ‖n‖ := by
    calc
      _ ≤ ‖d*x‖+‖n*y‖ := norm_add_le _ _
      _ ≤ max ‖d‖ ‖n‖*A+max ‖d‖ ‖n‖*B := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul (le_max_left _ _) hx (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _)))
          (mul_le_mul (le_max_right _ _) hy (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _)))
      _ = _ := by ring
  dsimp only
  rw [he,hdd,hd]
  exact ⟨hbound (hAb t hc).1 (hBb t hc).1,hbound (hAb t hc).2.1 (hBb t hc).2.1,
    hbound (hAb t hc).2.2 (hBb t hc).2.2⟩

#print axioms exists_continuous_atBot_halfLine_bound
#print axioms bubbleLowZeroCauchyLinear_halfLine_bound
end Yamabe3.Analysis.Delaunay
