import YM.FrontierTrace.Shear.Spacing
import YM.Pert.FirstTarget

/-!
Supply every *order0* ingredient of the two-radii contrast on the
FirstExtension scaling (weak, sparse; this does **not** yet cover all sufficiently
large real UV scales). Use the same Paying for both legs at one r. Contour at ν→∞
doesn't presume rate from label cap or Wick analytic comparison.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace Table Climb Next.UVStress Pert Maxwell Maxwell.Free UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order} (F:Spec.Final C f S)
    (Y:Scaling S) (ℓ:E4) (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0)
local notation "β0" => anomalyCoefficient G
local notation "A0" => theoryDensity G
local notation "T01" => metric0 C.labels 0 1
local notation "s0" => scalarLabel C.labels
variable (h:FirstExtension F Y)
include F h
-- in particular standard Yang--Mills weak-scale curve of Starting
lemma weak_paying : ∀ᶠ i in atTop, Paying F (Y.U i 4) := by
   filter_upwards [h.fit.hsym 4,h.fit.units 4] with i hi he; exact ⟨hi,he⟩

lemma weak_quote (i j:Axis): Tendsto (fun k=> (Y.U k 4).symm (Y.r k^4 • F.sector.energy i j)) atTop (𝓝 (metric0 C.labels i j)):=by
   simp_rw [metric0_eq_free, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact Pert.Scale.stress_readback h i j
lemma weak_translateAlpha (hG:G.Simple):∃ a:ℕ→ℝ,Tendsto a atTop (𝓝 1)∧
   ∀ᶠ k in atTop, ∀i j:Axis,i≠j→Y.r k^4 • F.sector.energy i j=a k • Y.U k 4 (metric0 C.labels i j):= by
   choose! a ha using fun i (hp:Paying F (Y.U i 4))=> offdiag_quotes F (Y.U i 4) hp hG (Y.r i)
   have hΘ:= metric_ne_zero C.labels hG
   have hm : ∀ᶠ i in atTop, (Y.U i 4).symm (Y.r i^4 • F.sector.energy 0 1) = a i • T01:= by
      filter_upwards [weak_paying F Y h] with i hi; rw [LinearEquiv.symm_apply_eq]; exact
        (ha _ hi _ _ (by decide)).trans (((Y.U i 4).toLinearMap.restrictScalars ℝ).map_smul ..).symm
   -- injective vector leads to scalar
   refine ⟨a,?_,(weak_paying F Y h).mono ha⟩
   have ht:=(weak_quote F Y h 0 1).congr' hm
   rw [tendsto_iff_norm_sub_tendsto_zero]; let t:=T01
   have hv : Tendsto (fun i:ℕ=>‖a i • t-t‖ / ‖t‖) atTop (𝓝 0):=by simpa [t] using! (ht.sub_const t).norm.div_const ‖t‖
   exact hv.congr fun i=>by
      rw [show a i • t-t = (a i-1) • t from by rw [sub_smul,one_smul],norm_smul]; exact
        mul_div_cancel_right₀ _ (norm_pos_iff.mpr hΘ|>.ne')
lemma weak_traction (hG:G.Simple) : F.sector.energy 0 1 ≠ 0 := by
   intro H; have ht:=weak_quote F Y h 0 1
   simp_rw [H,smul_zero,map_zero] at ht
   exact metric_ne_zero _ hG (tendsto_nhds_unique ht tendsto_const_nhds)

omit h in
lemma center_progress (P:Spin.change S 4)(hP : Paying F P) (x:S.Field 4) :
   centering (Bel C.book) 4 (P.symm (centering S 4 x)) = centering (Bel C.book) 4 (P.symm x):=by
   simp only [value_center (T:=S),map_sub,map_smul]
   rw [show P.symm (S.unit 4) = (Bel C.book).unit 4 from by rw [←hP.paid_unit, LinearEquiv.symm_apply_apply],Next.UVStress.const_out (Maxwell.Free.hierarchy C.labels).laws, smul_zero,sub_zero]
lemma weak_tau0 (hG:G.Simple):∃ d:ℕ→ℝ,Tendsto d atTop (𝓝 0)∧∀ᶠ k in atTop,
    Y.r k^4 • centered F=(4*d k) • scalarA (Y.U k 4) := by
   choose! d hd using fun k (hp:Paying F (Y.U k 4))=> centered_quote F (Y.U k 4) hp hG (Y.r k)
   let S':=Bel C.book; let D:=centering S' 4
   let S'' (k:ℕ):= (Y.U k 4).symm (Y.r k^4 • theta F 0)
   have hS' : D s0=s0 := by
      rw [show D s0=s0-expectation (Bel C.book) 4 s0 • (Bel C.book).unit 4 from value_center _]
      have he: expectation S' 4 s0=0:= by
         have hv: expectation (Bel C.book) 4 s0=first_value (S:=Bel C.book) 4 s0:=by rw [expectation,Work.A01.front_eval]; unfold first_value; congr 2; funext i; fin_cases i; rfl
         exact hv.trans mean_scalar_free
      rw [he,zero_smul,sub_zero]
   have hg : ∀ᶠ k in atTop, D (S'' k)= (4*d k) • s0 := by
      filter_upwards [weak_paying F Y h] with i hi; let P:=Y.U i 4
      change D (P.symm _) = _
      rw [← show D (P.symm (centering S 4 (Y.r i^4 • theta F 0)))=_ from center_progress F P hi _]
      rw [show centering _ _ (_ • _)=_ from ((centering S 4).restrictScalars ℝ).map_smul ..]
      change D (P.symm (Y.r i^4 • centered F)) = _
      rw [hd _ hi, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_smul,
        show D (P.symm (scalarA P)) = D s0 from (center_progress F P hi (P s0)).trans (congr_arg D (LinearEquiv.symm_apply_apply P s0)),hS']; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
   have ht : Tendsto S'' atTop (𝓝 0):= by
      have hh:=tendsto_finsetSum (f:=fun i k=> (Y.U k 4).symm (Y.r k^4 • F.sector.energy i i)) Finset.univ (fun i:Axis=>fun _=>weak_quote F Y h i i)
      have ho : ∑ i:Axis, metric0 C.labels i i=0:=by
         simp_rw [metric0, Finset.sum_neg_distrib]; rw [show ∑ i:Axis, canonicalStress C.labels i i=0 from by simpa only [UVNext.FreeStress.torch,one_smul] using torch_traceless C.labels 1, neg_zero]
      rw [ho] at hh; apply hh.congr
      intro k; unfold S''; simp only [theta,withoutMean,Complex.ofReal_zero,zero_smul,sub_zero, Finset.smul_sum,map_sum]
   have hv:= D.continuous_of_finiteDimensional.continuousAt.tendsto.comp ht
   rw [map_zero] at hv
   have hh: s0 ≠ 0:=money_ne_zero (C:=C) hG; have hf:= norm_pos_iff.mpr hh
   refine ⟨d,?_,(weak_paying F Y h).mono hd⟩
   rw [tendsto_iff_norm_sub_tendsto_zero]
   apply (show Tendsto (fun i:ℕ => ‖(4*d i) • s0‖/(4* ‖s0‖)) atTop (𝓝 0) from by simpa using! ((hv.congr' hg).norm.div_const (4*‖s0‖))).congr
   intro i; rw [norm_smul, norm_mul]; rw [Real.norm_eq_abs (r:=(4:ℝ))]; rw [sub_zero]; rw [abs_of_nonneg (by norm_num : (0:ℝ)≤4)]; field_simp

-- no all-orders fitting from FirstExtension
lemma weak_jets (n d j:ℕ)(R:ℝ): 0<R → Y.jets n d j R:=fun hp r _ v _ q _ _ hε=>
    h.jets r v q (fun _=> false) (fun _=>(0,0)) (window_closed ..) (fun _ h=>spaced_conf (inv_pos.mpr hp) h.1) hε

include ℓ hℓ in
lemma weak_scalar : ∃ ε:ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧ ∀ k t,t∈ [[(1:ℝ),2]] →
    ‖KK ℓ (Y.U k 4) (Y.r k) t - K0 G t‖ ≤ ε k:=by
   -- use actual leading jet theorem on compact shape
   let K: Set ℝ:= [[(1:ℝ),2]]; let z(t:ℝ):=atShape (t • ℓ)
   have hz: Continuous z:= (Work.A01.headDir 1).continuous.comp (by fun_prop : Continuous (fun t:ℝ=> t • ℓ))
   let A(k:ℕ):= Y.U k 4 s0; let W:=fun t:ℝ=> K0 G t
   let J:= z '' K
   let D(k:ℕ)(t:ℝ) := custom (Y.r k • z t) (A k) (A k); let M i:= first_value 4 (A i)
   let e i t := ‖KK ℓ (Y.U i 4) (Y.r i) t - W t‖
   have hS (t)(ht:t∈K) : 0<t:=zero_lt_one.trans_le (show 1≤t from by rw [show K=Icc 1 2 from uIcc_of_le (by norm_num)] at ht; exact ht.1)
   have he (t)(ht:t∈K): z t∈conf 2:=atRoom (aim_ne ℓ hℓ t (hS t ht))
   have hi(k): ContinuousOn (e k) K:= ContinuousOn.norm ((pure_smooth F ℓ (scalarA _) hℓ (Y.positive k)).sub (K0_cont G))
   obtain ⟨R,hR,H⟩:= ((Work.A05.compact_fits (isCompact_uIcc.image hz: IsCompact J) (image_subset_iff.mpr he)).and (eventually_gt_atTop 0)).exists
   have hM:=scalar_mean_leading Y (fun r=>weak_jets F Y h 1 4 0 r); rw [mean_scalar_free] at hM
   have ht : ∀ δ : ℝ,0<δ → ∀ᶠ k in atTop, ∀ t∈K,e k t<δ:= by
      intro δ hδ; have hh: ‖(0:ℂ)^2‖ < δ/2:=by simp only [zero_pow (show (2:ℕ)≠0 by decide),norm_zero]; positivity
      filter_upwards [(weak_jets F Y h 2 4 0 R H) 2 le_rfl 0 le_rfl scalarCompar (fun _=> le_rfl) _ (half_pos hδ), (hM.pow 2).norm.eventually (gt_mem_nhds hh)] with k hk hy t hK
      have hD : ‖D k t-W t‖ ≤ δ/2:= by
         rw [show W t = Ward.disc (scalarCompar (C:=C)) (z t) from (free_value G C.labels hℓ _ (hS t hK)).symm,
            show D k t=Ward.disc (Y.pins k ∘ (scalarCompar (C:=C))) (Y.r k • z t) from (scalar_expression Y _ _).symm]
         let r:= Y.r k; let u:= z t
         rw [← norm_iteratedFDeriv_zero (x:=u) (𝕜:=ℝ) (f:=fun u=> Ward.disc (Y.pins k ∘ scalarCompar) (r • u)-Ward.disc (scalarCompar (C:=C)) u)]
         apply le_trans (le_of_eq (congrArg norm ?_)) (hk (z t) (hR (mem_image_of_mem z hK)))
         ext x; simp only [sub_apply,iteratedFDeriv_zero_apply]; rfl -- might no goals
      unfold e; rw [show KK ℓ _ (Y.r k) t = D k t-(M k)^2 from ?_, sub_right_comm]
      · exact lt_of_le_of_lt (norm_sub_le ..) ((add_lt_add_of_le_of_lt hD hy).trans_eq (add_halves δ))
      unfold KK YM.FrontierTrace.pure scalarA
      rw [←focus_eq, mul_smul, ←onShape]; exact focus_read F.room.kernel _ (Work.A05.smul_conf (Y.positive k) (he _ hK))
   choose x hx hm using fun k=> isCompact_uIcc.exists_isMaxOn Set.nonempty_uIcc (hi k)
   refine ⟨fun k=> e k (x k),?_,fun k _ h=> hm k h⟩
   rw [Metric.tendsto_nhds]; intro u hu; filter_upwards [ht u hu] with i h
   rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]; exact h _ (hx i)
end YM.FrontierTrace
