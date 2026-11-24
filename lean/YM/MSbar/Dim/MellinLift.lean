import YM.MSbar.Symbol.CircleWeight
import YM.MSbar.Dim.Mellin

/-! Apply radial on AH symbols. This is NOT simply radial F for ε-dependent F by holding it fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Symbol Function Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {U : Set ℂ} {F : ℂ × (X × ℝ) → ℂ} {H K : ℝ}

lemma slope_AH (hf : AH U F) (hu : IsOpen U) : AH U (fun p : ℂ×X×ℝ => deriv (fun t=>F (p.1,p.2.1,t)) p.2.2) := by
    refine (hf.diff_smooth hu (0,0,1)).congr hu (fun z hz w=> ?_)
    have he := ((hf.smooth (z,w) hz).differentiableAt (by simp)).hasFDerivAt
    let y(t:ℝ):ℂ×X×ℝ:= (z,w.1,t);have hy : HasDerivAt y (0,0,1) w.2 := (hasDerivAt_const w.2 z).prodMk ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id' w.2))
    exact (he.comp_hasDerivAt w.2 hy).deriv.symm
lemma raising_AH (hf : AH U F) (hu : IsOpen U) : AH U (fun p : ℂ×X×ℝ => raised (fun t=>F (p.1,p.2.1,t)) p.2.2) := by
    let m:(X×ℝ)×ℝ→ X × ℝ:=fun p=>(p.1.1,p.2*p.1.2); have hm : m.HasTemperateGrowth:=by unfold m; fun_prop
    have he := (slope_AH (slope_AH hf hu) hu).arguments hm
    let μ:= volume.restrict (Icc (0:ℝ) 1);haveI:IsFiniteMeasure μ:= by unfold μ; infer_instance
    have h := he.after_average (p:=id) (w:=fun _=> ((↑(1/2:ℝ):ℂ))) (μ:=μ) (integrable_const _) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc
    exact h
lemma iterated_AH (hf : AH U F)(hu : IsOpen U)(n : ℕ) : AH U (fun p:ℂ×X×ℝ=> (raised^[n] (fun t=> F (p.1,p.2.1,t))) p.2.2) := by
    induction n with
    | zero => exact hf
    | succ n ih => simp_rw [iterate_succ_apply']; exact raising_AH ih hu

variable {t : ℂ→ℂ} (ht : DifferentiableOn ℂ t U) (hu : IsOpen U)
    (hf : AH U F) (hh : ∀ z∈U,∀ x, Radius H fun r=> F (z,x,r))
include ht hu hf hh
lemma mellin_after (hz : ∀ z∈ U,0 < (t z-1).re):
    AH U (fun p:ℂ × X=> rootM (fun u=> F (p.1,p.2,u)) (t p.1)):=by
    let w : ℝ × ℂ → ℂ:=fun p=> (↑p.1:ℂ)^(t p.2-1)
    have hp:= ht.analyticOnNhd hu; let K:=Icc (0:ℝ) (H^2)
    have he := AH.cauchy_average (μ:=volume) (w:=w) hu hf Real.continuous_sqrt (show IsCompact K from isCompact_Icc)
    have hx : ContinuousOn w (K ×ˢ U):=by
       intro x hx; exact ((Complex.continuousAt_ofReal_cpow x.1 (t x.2-1) (.inl (hz _ hx.2))).comp (f:=fun x:ℝ × ℂ=>(x.1,t x.2-1)) (continuousAt_fst.prodMk (((hp x.2 hx.2).continuousAt.comp continuousAt_snd).sub continuousAt_const))).continuousWithinAt
    have hd (a) (_ : a∈K) : DifferentiableOn ℂ (fun s=>w (a,s)) U:= fun s hs=> by change DifferentiableWithinAt ℂ (fun s => (↑a:ℂ)^(t s-1)) _ _; exact  (((hp s hs).differentiableAt.sub_const 1).const_cpow (Or.inr (by intro hE; have := hz s hs; change t s-1=0 at hE; simp [hE] at this))).differentiableWithinAt
    refine (he hx hd).congr hu fun z hz x=> ?_; dsimp only [w,K];rw [support_mellin (hh z hz x) le_rfl,intervalIntegral.integral_of_le (sq_nonneg _),integral_Icc_eq_integral_Ioc]
lemma stage_AH {n:ℕ} (hz : ∀ z∈ U,0 < (t z+n-1).re):
   AH U (fun p:ℂ×X=> stage (fun u => F (p.1,p.2,u)) n (t p.1)) := by
    let v(z:ℂ):= t z+n; have hv:DifferentiableOn ℂ v U:= ht.add_const _
    have he:= mellin_after hv hu (iterated_AH hf hu n) (fun z hz x=> (hh z hz x).repeat n) hz
    let g(z:ℂ):=(↑Real.pi:ℂ)^(t z)*(-1)^n* (Gamma (v z))⁻¹
    have h:DifferentiableOn ℂ g U:=by
       intro z hz
       exact (((((ht.analyticOnNhd hu z hz).differentiableAt.const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul_const _).mul ((differentiable_one_div_Gamma _).comp z ((hv.analyticOnNhd hu z hz).differentiableAt)))).differentiableWithinAt
    exact (AH.holomorphic hu h).mul he

lemma radial_AH : AH U (fun p:ℂ×X=> radial (fun u=> F (p.1,p.2,u)) (t p.1)) := by
    apply AH.locate; intro z hz; let n:= need (t z)+1;let V:={w : ℂ| 0<(t w+n-1).re}
    have he : V∈𝓝 z:= by
       refine ((show ContinuousAt (fun w=>(t w+n-1).re) z from continuous_re.continuousAt.comp (((ht.analyticOnNhd hu z hz).continuousAt.add_const _).sub continuousAt_const)).tendsto.eventually ?_)
       apply lt_mem_nhds; simp only [sub_re,add_re,n,Nat.cast_add,Nat.cast_one,one_re,natCast_re]; linarith only [enough (t z)]
    obtain ⟨A,ha,hA,H'⟩:= _root_.mem_nhds_iff.mp (inter_mem he (hu.mem_nhds hz)); have hu': A⊆U:=ha.trans inter_subset_right
    have hv':∀ z∈A,0<(t z+n-1).re:= fun z hz => (ha hz).1
    refine ⟨A,H',(stage_AH (ht.mono hu') hA (hf.upon hu') (fun z hz=> hh z (hu' hz)) hv').congr hA (fun z hz x=> (formula (hh z (hu' hz) x) (by have hh:= hv' z hz; simp at hh; linarith)).symm)⟩
end YM.MSbar.Dim
