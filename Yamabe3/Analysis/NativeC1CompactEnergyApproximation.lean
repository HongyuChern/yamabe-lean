import Yamabe3.Analysis.NativeWeakChartCompletion
import Yamabe3.Analysis.NativeC1CollarTraceBound
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation

/-! Compact C1 data have an actual smooth energy approximation and the
same literal value trace. The trace limit follows from the annular C1
estimate, not from restriction of a volume almost-everywhere equality. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Topology ContDiff ENNReal RealInnerProductSpace Manifold
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak UniformElliptic
local notation "D" => nativeWeakEuclideanD

theorem native_C1_compact_memH01 {O:Set E} (hO:IsOpen O)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u) (hc:HasCompactSupport u) (hs:tsupport u⊆O) :
    MemH01 u O := by
  have hv:MemLp u 2 (volume.restrict O) := (hu.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hd(i:Fin 3):MemLp (fun x=>fderiv ℝ u x (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict O
  have hH:MemW1p 2 u O := ⟨hv,fun i=>⟨_,hd i,
    native_hasWeakPartialDeriv_of_contDiffOn_one hO hu.contDiffOn i⟩⟩
  simpa using memW01p_of_memW1p_of_tsupport_subset hO (p:=2) (by norm_num)
    (by simpa using hH) hc hs

theorem native_C1_annulus_value_bound {a b r:ℝ} (ha:0<a) (hab:a<b) (hr:r∈Icc a b)
    {O:Set E} (hKO:EuclideanSphereTrace.sphereTraceAnnulus a b⊆O)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u)
    (hv:MemLp u 2 (volume.restrict O))
    (hd:∀i:Fin 3,MemLp (fun x=>fderiv ℝ u x (EuclideanSpace.single i 1)) 2 (volume.restrict O)) :
    (∫θ:S,u (r • (θ:E))^2 ∂angularVolume) ≤
      (2/((b-a)*a^2))*max 1 ((b-a)^2)*
        ((∫x in O,u x^2)+∑i:Fin 3,∫x in O,(fderiv ℝ u x (EuclideanSpace.single i 1))^2) := by
  let K:=EuclideanSphereTrace.sphereTraceAnnulus a b
  let M:=max (1:ℝ) ((b-a)^2)
  let e:=fun x:E=>u x^2+∑i:Fin 3,(fderiv ℝ u x (EuclideanSpace.single i 1))^2
  have he:IntegrableOn e O := hv.integrable_sq.add (integrable_finsetSum _ (fun i _=>(hd i).integrable_sq))
  have hi:IntegrableOn (EuclideanSphereTrace.scaledSphereTraceEnergy (b-a) u) K :=
    ((hu.continuous.pow 2).add (continuous_const.mul ((hu.continuous_fderiv (by norm_num)).norm.pow 2))).continuousOn.integrableOn_compact
      (EuclideanSphereTrace.isCompact_sphereTraceAnnulus a b)
  have hpt(x:E):EuclideanSphereTrace.scaledSphereTraceEnergy (b-a) u x ≤ M*e x := by
    unfold EuclideanSphereTrace.scaledSphereTraceEnergy
    rw [native_fderiv_norm_sq_eq_partials]
    have h0:=mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) ((b-a)^2)) (sq_nonneg (u x))
    have h1:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) ((b-a)^2))
      (show 0 ≤ ∑i:Fin 3,nativeCoordinateFirst i u x^2 from Finset.sum_nonneg (fun i _=>sq_nonneg _))
    dsimp only [M,e,nativeCoordinateFirst] at *
    nlinarith only [h0,h1]
  have hle:=integral_mono hi ((he.mono_set hKO).const_mul M) hpt
  rw [integral_const_mul] at hle
  have hinc:=setIntegral_mono_set he
    (Eventually.of_forall fun x=>add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _=>sq_nonneg _)))
    (Eventually.of_forall fun x=>@hKO x)
  have htrace:=EuclideanSphereTrace.integral_sphere_restriction_sq_le_scaled_annulus_energy_C1
    ha hab hr isOpen_univ (subset_univ _) hu.contDiffOn
  simp only [EuclideanSphereTrace.angularVolume,polar_sphereMeasure_eq_native] at htrace
  have hM:0 ≤ M := zero_le_one.trans (le_max_left _ _)
  have hC:0 ≤ 2/((b-a)*a^2) := by positivity
  have hfinal:=htrace.trans (mul_le_mul_of_nonneg_left
    (hle.trans (mul_le_mul_of_nonneg_left hinc hM)) hC)
  simpa only [e,integral_add hv.integrable_sq (integrable_finsetSum _ (fun i _=>(hd i).integrable_sq)),
    integral_finsetSum _ (fun i _=>(hd i).integrable_sq),M,mul_assoc] using hfinal

theorem exists_native_C1_compact_energy_approximation {O:Set E} (hO:IsOpen O)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u) (hc:HasCompactSupport u) (hs:tsupport u⊆O) :
    ∃(z:H1Zero D O) (φ:ℕ→EnergyTest D O),
      (toL2 D O z:E→ℝ)=ᵐ[volume] O.indicator u ∧
      Tendsto (fun n=>(φ n:H1Zero D O)) atTop (𝓝 z) ∧
      ∀ a b r : ℝ, 0 < a → a < b → r ∈ Icc a b → EuclideanSphereTrace.sphereTraceAnnulus a b ⊆ O →
        Tendsto (fun n=>∫θ:S,(φ n (r • (θ:E))-u (r • (θ:E)))^2 ∂angularVolume) atTop (𝓝 0) := by
  classical
  have hH:=native_C1_compact_memH01 hO hu hc hs
  obtain ⟨z,hz⟩:=exists_nativeEuclideanH01_of_memH01 hO hH
  rcases hH with ⟨_,w,ψ,hψ,hcψ,hsψ,hv,hd⟩
  let φ(n:ℕ):EnergyTest D O:=⟨ψ n,(hψ n).contMDiff,hcψ n,hsψ n⟩
  have hzlim:=nativeEuclidean_approximation_tendsto_to_rep hO φ u w.weakGrad
    w.memLp w.weakGrad_component_memLp hv hd z hz
  refine ⟨z,φ,hz,hzlim,?_⟩
  intro a b r ha hab hr hKO
  have hdu(i:Fin 3):MemLp (fun x=>fderiv ℝ u x (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict O
  have hsame(i:Fin 3): (fun x=>w.weakGrad x i)=ᵐ[volume.restrict O]
      (fun x=>fderiv ℝ u x (EuclideanSpace.single i 1)) :=
    HasWeakPartialDeriv.ae_eq hO (w.isWeakGrad i)
      (native_hasWeakPartialDeriv_of_contDiffOn_one hO hu.contDiffOn i)
      ((w.weakGrad_component_memLp i).locallyIntegrable (by norm_num)) ((hdu i).locallyIntegrable (by norm_num))
  have hd'(i:Fin 3):Tendsto (fun n=>eLpNorm
      (fun x=>fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict O)) atTop (𝓝 0) := by
    have he(n:ℕ):eLpNorm (fun x=>fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1))
        2 (volume.restrict O)=eLpNorm (fun x=>fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-w.weakGrad x i)
        2 (volume.restrict O) := by
      apply eLpNorm_congr_ae
      filter_upwards [hsame i] with x hx
      rw [hx]
    simpa only [he] using hd i
  let hm(n:ℕ):MemLp (ψ n) 2 (volume.restrict O):=
    ((hψ n).continuous.memLp_of_hasCompactSupport (hcψ n)).restrict O
  let hdm(n:ℕ)(i:Fin 3):MemLp (fun x=>fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) 2 (volume.restrict O):=
    (nativeEuclidean_test_derivative_memLp O (φ n) i).restrict O
  have hval:Tendsto (fun n=>∫x in O,(ψ n x-u x)^2) atTop (𝓝 0) := by
    have hl:=((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm _ w.memLp).mpr hv).sub (tendsto_const_nhds (x:=w.memLp.toLp u))
    simpa only [native_norm_toLp_sub_sq_eq_integral_sq,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using hl.norm.pow 2
  have hgrad(i:Fin 3):Tendsto (fun n=>∫x in O,
      (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1))^2) atTop (𝓝 0) := by
    have hl:=((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n=>hdm n i) _ (hdu i)).mpr (hd' i)).sub (tendsto_const_nhds (x:=(hdu i).toLp (fun x=>fderiv ℝ u x (EuclideanSpace.single i 1))))
    simpa only [native_norm_toLp_sub_sq_eq_integral_sq,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using hl.norm.pow 2
  have hsum:=hval.add (tendsto_finsetSum Finset.univ (fun i _=>hgrad i))
  simp only [Finset.sum_const_zero,add_zero] at hsum
  have hbnd(n:ℕ): (∫θ:S,(φ n (r • (θ:E))-u (r • (θ:E)))^2 ∂angularVolume) ≤
      (2/((b-a)*a^2))*max 1 ((b-a)^2)*
        ((∫x in O,(ψ n x-u x)^2)+∑i:Fin 3,∫x in O,
          (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1))^2) := by
    have hfd(i:Fin 3): (fun x=>fderiv ℝ (fun y=>ψ n y-u y) x (EuclideanSpace.single i 1))=
        (fun x=>fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1)) := by
      funext x
      rw [fderiv_fun_sub ((hψ n).differentiable (by simp)).differentiableAt
        (hu.differentiable (by norm_num)).differentiableAt]
      rfl
    have hh:=native_C1_annulus_value_bound ha hab hr hKO ((hψ n).of_le (by simp) |>.sub hu)
      ((hm n).sub w.memLp) (fun i=>by rw [hfd]; exact (hdm n i).sub (hdu i))
    have hfdp(i:Fin 3)(x:E):fderiv ℝ (fun y=>ψ n y-u y) x (EuclideanSpace.single i 1)=
        fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)-fderiv ℝ u x (EuclideanSpace.single i 1):=congrFun (hfd i) x
    simpa only [hfdp,φ] using hh
  exact squeeze_zero (fun n=>integral_nonneg (fun θ=>sq_nonneg _)) hbnd
    (by simpa only [mul_zero] using hsum.const_mul ((2/((b-a)*a^2))*max 1 ((b-a)^2)))

#print axioms native_C1_compact_memH01
#print axioms native_C1_annulus_value_bound
#print axioms exists_native_C1_compact_energy_approximation
end Yamabe3.Analysis.SpherePolar
