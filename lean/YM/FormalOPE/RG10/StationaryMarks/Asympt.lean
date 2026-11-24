import YM.FormalOPE.RG10.StationaryMarks.OnDisc
/-!
 # Budget outside s patch & base expansion (constant prices coefficients).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I:Type}[Fintype I]
local notation "μ"=>physical G I
local notation "ν"=>tangent G I
local notation "E"=>Direction G I
variable {P:ChartRatio G}{A O:Spending G I}
lemma rapid {c:ℝ}(hc:0<c)(d n:ℕ):∃ R:ℝ, 0≤R ∧ ∀ t:ℝ,0<t → (t^d)⁻¹ * Real.exp (-c/t^2)≤ R*t^n:= by
 obtain ⟨R,hr,H⟩:= bounded_exp hc (d+n); refine ⟨R,hr,fun t ht=>?_⟩
 have he: (t^d)⁻¹*Real.exp (-c/t^2)*(t⁻¹)^n=(t⁻¹)^(d+n)*Real.exp (-c*(t⁻¹)^2):= by rw [←inv_pow,div_eq_mul_inv,← inv_pow,pow_add]; ring
 apply le_of_mul_le_mul_right (a:=(t⁻¹)^n) _ (by positivity); rw [he, show R*t^n*(t⁻¹)^n=R from by rw [mul_assoc,← mul_pow,mul_inv_cancel₀ ht.ne',one_pow,mul_one]]
 exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le).trans (H t⁻¹ (by positivity))
variable (L:LocalRatio P)(C:Credential A) (h:Curtain O)
include L C h in
lemma exteriorized {r:ℝ}(hr:r<small G P)(hp: 0<r) (n:ℕ): Tested.Bill n
 (fun t=> scale G I t * ∫ u in (chamber G I r)ᶜ,dollar A O t u ∂μ):= by
 let S:= chamber G I r
 have hv:IsOpen S:= Ratio.chamber_open L hr.le; have hs:= hv.measurableSet
 have ha: (1:Configuration G I)∈S:= fun u _=>⟨0,mem_ball_self hp,G.mat_lieExp_zero⟩
 obtain ⟨b,hb,H⟩:= C.cut S (hv.mem_nhds ha)
 obtain ⟨R,hr',hR⟩:= rapid hb (Module.finrank ℝ E) n
 obtain ⟨M,hm⟩:= h.bounded; have hn:0≤M:=(norm_nonneg _).trans (hm 1)
 refine ⟨M * R,by positivity, ?_⟩; filter_upwards [Tested.eventually_pos] with t ht
 let c:= M*Real.exp (-b/t^2); have hc:0≤c:= mul_nonneg hn (Real.exp_pos _).le
 have hi: Integrable (fun _ : Configuration G I=> c) μ:= integrable_const c
 have hh: ‖∫ u in Sᶜ,dollar A O t u ∂μ‖ ≤ c:= by
   refine (norm_integral_le_of_norm_le (g:=fun _=>c) hi.integrableOn ?_).trans ((setIntegral_le_integral hi (Filter.Eventually.of_forall fun _=>hc)).trans_eq (by simp))
   filter_upwards [ae_restrict_mem hs.compl] with u hu
   unfold dollar; rw [norm_mul,Real.norm_eq_abs (Real.exp ..),abs_of_pos (Real.exp_pos _)]
   exact mul_le_mul (hm u) (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (le_of_not_gt (fun he=>hu (H _ he)))) (sq_nonneg _))) (Real.exp_pos _).le hn
 have hq:0≤scale G I t:= by unfold scale; positivity
 rw [norm_mul,Real.norm_eq_abs (scale ..),abs_of_nonneg hq]; apply le_trans (mul_le_mul_of_nonneg_left hh hq)
 change _ * (M*_) ≤ _; rw [mul_left_comm, mul_assoc]; exact mul_le_mul_of_nonneg_left (hR t ht) hn

include L C h in
lemma base : Aspiration (journal A O) (summing P A O):= by
 intro n
 have ha:= Stationary.rescale_estimate ν (F:=C.centered) (hf:=(show ContDiffAt ℝ ∞ (offer P O) 0 from ((Ratio.jacobian_smooth L).of_le le_top).mul h.germ)) ((Ratio.jacobian_meas L).mul (h.meas.comp expLinks_meas)) (C.meas.comp expLinks_meas) C.boundedBy n
 obtain ⟨d,hd,hb⟩:= ha
 let r:= min d (small G P) / 2
 have hp:0<r:= half_pos (lt_min hd (Ratio.small_pos L)); have hr:r<small G P:= lt_of_lt_of_le (half_lt_self (lt_min hd (Ratio.small_pos L))) (min_le_right ..)
 obtain ⟨D,H⟩:= hb r ⟨hp,(half_lt_self (lt_min hd (Ratio.small_pos L))).trans_le (min_le_left ..)⟩
 obtain ⟨R,hr',hz⟩:= exteriorized L C h hr hp (n+1)
 refine ⟨|D|+R,by positivity,?_⟩
 filter_upwards [Tested.eventually_pos, hz, H] with t ht hy hk
 let g:=dollar A O t; let S:=chamber G I r
 have he: (journal A O - peval (summing P A O) n) t = (partialSum ν (offer P O) (A∘ expLinks G I) r t - peval (summing P A O) n t) + scale G I t * ∫ x in Sᶜ,g x ∂μ:= by
   rw [Pi.sub_apply,journal,← integral_add_compl (s:=S) ((Ratio.chamber_open L (U:=I) hr.le).measurableSet) (endowment C h t),mul_add, show S=chamber G I r from rfl, interiorized C h L ht hr hp]; dsimp only [g]; abel
 rw [he,add_mul]
 refine (norm_add_le ..).trans (add_le_add (le_trans ?_ (mul_le_mul_of_nonneg_right (le_abs_self D) (pow_nonneg ht.le _))) hy)
 exact hk

include L C in
lemma upfront : 0<summing P A 1 0:= by
 let a:=normTerm (offer P (O:=1) (G:=G) (I:=I)) (A ∘ expLinks G I) 0
 have he (u:E): a u= (jacobian P (U:=I) 0) * kernel (A ∘ expLinks G I) u:= by
    have h₀: Finset.antidiagonal (0:ℕ)={(0,0)}:= by ext ⟨x,y⟩; simp
    simp [a,normTerm,integrandSeries,Zone.mul,h₀, offer, Zone.TaylorPow, expsum]
 have hb: Integrable a ν:= C.centered.integrableTerm ν (K:=offer P 1) (by exact (((Ratio.jacobian_smooth L).of_le le_top).mul (show Curtain (1:Spending G I) from Inherit.unit).germ)) C.boundedBy
 have hz:∀ u,0<a u:= fun u=> by rw [he]; exact mul_pos (Finset.prod_pos fun i _=>(show 0<fee P 0 from lt_max_of_lt_left (by rw [L.anchored,mul_one];exact L.scale))) kernel_pos
-- IsAddHaar univ positive; use open positive
 apply (integral_pos_iff_support_of_nonneg (fun u=> (hz u).le) hb).mpr
 rw [Set.eq_univ_of_forall (s:=Function.support a) (fun x=> (hz x).ne')]; exact isOpen_univ.measure_pos ν Set.univ_nonempty
end YM.FormalOPE.RG10.StationaryMarks
