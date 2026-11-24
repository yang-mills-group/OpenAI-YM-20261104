import YM.Juniper.Cinch.Shipping
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
/-! Every requirement before markets. unbounded true period OK; support prices beat any and all fixed precision requests. Uniform all N at actual Levels; AUX Mini recursively must instead take its calibrated shift OR supply beta k exact.
 -/
open Filter Function Lattice RG Pressure Pressure.Testing Tree Wilson
open Push Push.AbsoluteSums Precision Next.Fluctuations SectorMeasure
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Coat Rain
open Further.PhysicalPeriodLimitF933 Macrame Uniform
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Input Org Supply Opera Pane Roof Push.PriceCompiler ThroughLaunch Blaze Roost Push.Uniform
open Progress.DirectedRecipe Time
open scoped InnerProductSpace
set_option quotPrecheck false
variable {σ H:ℝ}
local notation "s"=> (c.val:ℝ)
local notation "d"=> (turnB W c:ℝ)
local notation "t"=> W.threshold
lemma glimpse {r:ℝ} (hr:1<r): (Pressure.radiusB r:ℝ) ≤ 2*r^2:= by
   unfold Pressure.radiusB; refine (Nat.ceil_lt_add_one (sq_nonneg (Real.log r))).le.trans ?_; nlinarith only [Real.log_pos hr,sq_le_sq₀ (Real.log_pos hr|>.le) (by linarith only [hr]:0 ≤ r) |>.mpr (by linarith only [Real.log_le_sub_one_of_pos (by linarith only [hr] : 0 < r)]), one_le_pow₀ hr.le (n:=2)] -- (n:=2) parameter syntax
lemma launches {r:ℝ}(hn:20<c.val)(he: W.B=Pressure.radiusB r)(hr:1<r)(ht:(1000*r^2)^2 ≤ s) : Real.sqrt s ≤ d:= by
    have hy : 2 ≤ s:= by exact_mod_cast (show 2 ≤ c.val from by omega) -- edit
    have hb:=glimpse hr; rw [← he] at hb; have hi:0 ≤ s:=by positivity
    let f:= Real.sqrt s; have hh : 1≤f:= Real.one_le_sqrt.mpr (by linarith); have he: 1000*r^2 ≤ f := (Real.le_sqrt (by positivity) hi).2 ht;
    by_contra! hx; have hv:= Cinch.rising W hn; have hc: 100*(W.B:ℝ)+20 ≤ f:= by nlinarith only [he,hb,one_le_pow₀ hr.le (n:=2)]
    change d<f at hx; have ht : 100*(W.B:ℝ)*f ≤ f^2:= by nlinarith only [mul_le_mul_of_nonneg_right hc (by linarith only [hh] : 0≤f),hh]
    have he':=(mul_le_mul_of_nonneg_right hh (show 0≤(W.B:ℝ) by positivity)); have hz : f^2=s:=Real.sq_sqrt hi
    nlinarith only [he',hv,hz,(mul_lt_mul_of_pos_left hx (by positivity :0 < 4*(W.B:ℝ)+2)),ht,mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ W.B from Nat.one_le_cast.mpr W.B_pos) (zero_le_one.trans hh)]
def wraps (r:ℝ) (c:Side):= (1000*r^2)^2 ≤ (c.val:ℝ)
lemma affair (h:0 ≤ H)(he: |σ| ≤ turnFeeP W c * H) (hp: Real.sqrt s ≤ d) :
   W.threshold^2* |σ| ≤ H*(3*s^10) *Real.exp (- Real.sqrt s) ∧
   forecastW G c W σ ≤ H*(3*s^14)*(Fintype.card Signed:ℝ)*((Fintype.card PlaqAxes:ℝ)*VerifiedReset.pairBill G W)* Real.exp ((W.supportExponent+1)*81)* Real.exp (- Real.sqrt s):= by
   have ht:=W.threshold_pos; have hg:= W.exponent_pos
   let u:=(3:ℝ)*s^10; let r:=Real.exp (-(preExponent W*d)); let f:= turnFeeP W c; let X:=W.supportExponent; let v:= Real.exp ((X+1)*81); have hk:f=(u/t^2)*r:= by unfold f turnFeeP fare u r; rw [site_card]; push_cast; ring
   have hz : t^2* |σ| ≤ H*u*r:= by change |σ|≤ f*H at he; rw [hk] at he; apply (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq; field_simp
   have hL: r * Real.exp ((X+1)*(d+81)) ≤ v * Real.exp (-Real.sqrt s) := by unfold r v; rw [← Real.exp_add,←Real.exp_add]; apply Real.exp_le_exp.mpr; change -((X+3)*d)+ _ ≤_; linarith only [hp,Nat.cast_nonneg (α:=ℝ) (turnB W c)]
   have hR : r ≤ Real.exp (-Real.sqrt s) := Real.exp_le_exp.mpr (by unfold preExponent; nlinarith only [hp,mul_nonneg hg.le (Nat.cast_nonneg (α:=ℝ) (turnB W c)),Nat.cast_nonneg (α:=ℝ) (turnB W c)])
   refine ⟨hz.trans (mul_le_mul_of_nonneg_left hR (by unfold u; positivity)),?_⟩; have ht:= VerifiedReset.pair_nonneg G W
   let p:=(Fintype.card PlaqAxes:ℝ)*VerifiedReset.pairBill G W; let y:=(X+1)*(d+81); let x:=(Fintype.card Signed:ℝ)*s^4
   unfold forecastW Pylon.droop Pylon.headBill; rw [show Fintype.card (Seat c)=Fintype.card Signed*c.val^4 from Fintype.card_prod _ _|>.trans (congrArg _ (site_card _))]; push_cast
   change x*(|σ| * (p*t^2)*Real.exp y) ≤ _; calc _ = t^2*|σ| *(x*p*Real.exp y):= by ring
                                                  _ ≤ (H*u*r)*(x*p*Real.exp y):= mul_le_mul_of_nonneg_right hz (by unfold x p; positivity)
                                                  _ = (H*u*(x*p))*(r* Real.exp y):= by ring
                                                  _ ≤ _ := (mul_le_mul_of_nonneg_left hL (show 0≤H*u*(x*p) by unfold x u p; positivity)).trans_eq (by unfold v u x X p; ring)
section stage
variable (G:Gauge)(P:RG.Stage)(n:ℕ)
def scrutiny (x:ℝ): Prop:= 1 ≤ x∧∀ c:Side,20<c.val→wraps x c→∀ P':BudgetPoint,Time.Same P P'→P'.B=radiusB x→ ∀ σ H:ℝ,0≤ H→ |σ| ≤ turnFeeP P' c * H→P'.threshold^2*|σ|≤ H/ (4*x^n) ∧ forecastW G c P' σ≤ H/(4*x^n)
lemma scrutiny_pays: ∀ᶠ x in atTop,scrutiny G P n x:= by
    let Q:=(Fintype.card Signed:ℝ)*((Fintype.card PlaqAxes:ℝ)*VerifiedReset.pairBill G (Time.probe P))* Real.exp ((P.supportExponent+1)*81)
    have hq :0 ≤ Q:=by unfold Q; have ht:= VerifiedReset.pair_nonneg G (Time.probe P); positivity
    have hh(q:ℝ)(k:ℕ): ∀ᶠ x in atTop, (12*q)*(x^(k+n))*Real.exp (-Real.sqrt x) ≤ 1:= by
       have he:= (isLittleO_pow_exp_pos_mul_atTop (2*(k+n)) (b:=(1:ℝ)) zero_lt_one).tendsto_div_nhds_zero.comp Real.tendsto_sqrt_atTop
       filter_upwards [(he.const_mul (12*q)).eventually (gt_mem_nhds (show 12*q*0<1 from by simp)),eventually_gt_atTop (0:ℝ)] with x hp hx; apply le_of_lt; rw [← Real.sq_sqrt (show 0≤x from hx.le)] -- risky rewrites
       dsimp only [Function.comp_apply] at hp
       rw [div_eq_mul_inv,pow_mul,Real.sq_sqrt hx.le,one_mul] at hp; rw [Real.sq_sqrt hx.le, Real.exp_neg,mul_assoc]; exact hp
    obtain ⟨v,hv⟩:= eventually_atTop.mp ((hh 1 10).and (hh Q 14)); filter_upwards [eventually_ge_atTop v,eventually_gt_atTop (1:ℝ)] with x hv' h; refine ⟨h.le,fun c hc hh P' hr hp σ H hH hs=>?_⟩
    have he: (x:ℝ) ≤ (c.val:ℝ):=by have hy: 1≤x^2:= one_le_pow₀ h.le; have ht: x ≤ x^2:= le_self_pow₀ h.le (by decide); exact le_trans (by nlinarith only [ht,hy] : x ≤ (1000*x^2)^2) hh
    obtain ⟨hz,hK⟩:= affair (G:=G) hH hs (launches hc hp h hh)
    let p (q:ℝ)(k:ℕ):= H*(3*(c.val:ℝ)^k)*Real.exp (-Real.sqrt (c.val:ℝ))*q -- need type nat q real
    have hf := (hv (c.val:ℝ) (hv'.trans he)); have hF :VerifiedReset.pairBill G P'=VerifiedReset.pairBill G (Time.probe P):= by unfold VerifiedReset.pairBill Time.probe; dsimp only; rw [hr.1,hr.2.1]
    have hX:= Real.exp_pos (-Real.sqrt (c.val:ℝ))
    have hu(q:ℝ)(k:ℕ)(hQ:0≤q)(h: (12*q)*((c.val:ℝ)^(k+n))*Real.exp (-Real.sqrt (c.val:ℝ)) ≤ 1) : p q k ≤ H/(4*x^n):= by
       have hi:1<x:= ‹1<x›; apply (le_div_iff₀ (by positivity)).mpr; dsimp only [p]; rw [pow_add] at h; apply le_trans _ (show H*(12*q*((c.val:ℝ)^k*(c.val:ℝ)^n)*Real.exp (-Real.sqrt (c.val:ℝ))) ≤ H from mul_le_of_le_one_right hH h); calc _ ≤ H*(3*(c.val:ℝ)^k)*Real.exp (-Real.sqrt (c.val:ℝ))*q*(4*(c.val:ℝ)^n):= by gcongr
                                                                                                                                                                                     _ = _ := by ring
    refine ⟨hz.trans (?_), hK.trans ?_⟩; · simpa only [p,mul_one] using! hu 1 10 zero_le_one hf.1
    rw [hF,hr.2.2]; apply le_trans _ (hu Q 14 hq hf.2); unfold p Q; apply le_of_eq; ring
end stage
end YM.Juniper.Cinch
