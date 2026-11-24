import YM.SignedWilsonExpansion.Purchase.Rights
import YM.SignedWilsonExpansion.F9.GradesW
import YM.Next.RANK.NoSpill
/-! # Currency calibration.Asymptotic prices for cohorts.Stable under ordered restriction.
 Backbone (`B`≈β_*). polynomial Y = log B. Use of M after convergence. precision growth receipts ask after lengths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.UVClock
open Asymptotics Wilson Gauge RG Push Lattice Source
open WilsonCoeffUV.Bank
open Set Filter Function Real Next.Rank Perch Commission
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}{ι κ:Type*}{A K S Q B:ι→ℝ}{L:Filter ι}
abbrev Rise (x:ι→ℝ) (L:Filter ι):Prop:= Tendsto x L atTop
variable (h:Rise B L)
abbrev dollar (B:ι→ℝ):ι→ℝ:=fun i=> Perch.bill 1 (B i)
abbrev cent (B:ι→ℝ):ι→ℝ:=fun i=> Perch.bill (-1/2) (B i)
abbrev mark (B:ι→ℝ):ι→ℝ:=fun i=> (Real.sqrt (B i))⁻¹
abbrev Spread (B:ι→ℝ):ι→ℝ:= fun i=>Real.log (B i)
theorem dnote (A:Levels G)(i:ℕ): A.clock.monitor i = Perch.bill 1 (A.clock.hatBeta i):=by rw [Perch.bill,mul_one]; rfl
theorem hedge (a b:ℝ): 0 < Perch.bill a b:= Real.exp_pos _
theorem dollar_ge (x:ℝ): 1 ≤Perch.bill 1 x:=by unfold Perch.bill; rw [mul_one]; exact Real.one_le_exp ( Perch.boil_pos _ )
theorem penny (x:ℝ): (Perch.bill 1 x)⁻¹= Perch.bill (-1/2) x * Perch.bill (-1/2) x:=by rw [overlap,Perch.bill,mul_one,← Real.exp_neg,show -(1:ℝ)/2+ -1/2= -1 by ring, Perch.bill]; congr 1; ring
theorem ss_nifty (A:Levels G)(i:ℕ): (Real.sqrt (A.clock.monitor i))⁻¹= Perch.bill (-1/2) (A.clock.hatBeta i):=by rw[dnote,← Real.sqrt_inv,penny,Real.sqrt_mul_self (hedge _ _|>.le)]
include h
theorem y_rise : Rise (Spread B) L:= Real.tendsto_log_atTop.comp h
theorem M_rise : Rise (dollar B) L:= (Perch.bill_lo zero_lt_one).comp h
theorem θ_small : Tendsto (cent B) L (𝓝 0):= (Perch.bill_hi (a:=-1/2) (by norm_num)).comp h
theorem mark_sold (n:ℕ): Tendsto (fun i=> (dollar B i)^n * mark B i) L (𝓝 0):=by
    let S(n:ℕ)(i):= (dollar B i)^n * mark B i
    have h0:Tendsto (fun i=> Real.exp (-(Spread B i)/4)) L (𝓝 0):= Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp (y_rise h)).atBot_div_const (by norm_num: (0:ℝ)<4)); refine squeeze_zero' (Eventually.of_forall fun i=> (?_ : 0≤(dollar B i)^n * mark B i)) (?_) h0
    · exact mul_nonneg (pow_nonneg (hedge 1 (B i)|>.le) _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    filter_upwards [h.eventually (Paint.monitors (n:ℝ) (1/4) (by norm_num)),h.eventually_gt_atTop 0] with i hi hp
    dsimp only [dollar,mark,Spread]; rw [show (Real.sqrt (B i))⁻¹=_ from Paint.logged (B i) hp, Perch.bill,mul_one, ← Real.exp_nat_mul,← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hi])
theorem dollar_credit (B':Credit): Tendsto (fun i=> B'.buy (dollar B i) * mark B i) L (𝓝 0):=by have hx:=(mark_sold h B'.d).const_mul B'.x; simpa only [Credit.buy,mul_assoc,mul_zero] using hx
theorem daybreak (n:ℕ) : Tendsto (fun i=> (Spread B i)^n * cent B i) L (𝓝 0):=by
    let t(i):= Real.log (Spread B i); have ht:Rise t L:= Real.tendsto_log_atTop.comp (y_rise h); let x'(i):= t i*(n - t i/2); have hx:Tendsto x' L atBot:=by refine Filter.Tendsto.atTop_mul_atBot₀ ht (g:=fun i=> n - t i/2) (tendsto_atBot.2 fun a=>?_); filter_upwards [ht.eventually_ge_atTop (2*((n:ℝ)-a))] with i hi; linarith
    refine (Real.tendsto_exp_atBot.comp hx).congr' ?_; filter_upwards [(y_rise h).eventually_gt_atTop 0] with i hi; change Real.exp _ = _; rw [show x' i=n*(t i)+(t i)^2 * (-1/2) from by unfold x'; ring, exp_add,exp_nat_mul,show exp (t i)=_ from (exp_log hi : exp (t i)= _)]; rfl
theorem dayCredit (C:Credit): Tendsto (fun i=> C.buy (Spread B i)* cent B i ) L (𝓝 0):=by have hx:=(daybreak h C.d).const_mul C.x; simpa only [Credit.buy,mul_assoc,mul_zero] using hx
variable (p: IsEquivalent L A B)
include p
lemma tends : Rise A L:= p.symm.tendsto_atTop h
lemma log_tie : Tendsto (fun i=> Spread A i-Spread B i) L (𝓝 0):=by
    let z:= (isEquivalent_iff_tendsto_one ((h.eventually_gt_atTop 0).mono fun _ h=>h.ne')).1 p; have he:= ( Real.continuousAt_log (show (1:ℝ)≠0 from one_ne_zero)).tendsto.comp z; rw [Real.log_one] at he; refine he.congr' ?_; filter_upwards [h.eventually_gt_atTop 0,( tends h p).eventually_gt_atTop 0] with i hp hx; exact Real.log_div hx.ne' hp.ne'
lemma spread_tie : IsEquivalent L (Spread A) (Spread B):=by apply isEquivalent_of_tendsto_one; have hp:= (log_tie h p).div_atTop (y_rise h)|>.add_const 1 ; rw [zero_add] at hp; apply hp.congr'; filter_upwards [(y_rise h).eventually_gt_atTop 0] with i hi using (by rw [Pi.div_apply]; rw [sub_div,div_self hi.ne',sub_add_cancel])
lemma sqrt_tie : IsEquivalent L (Real.sqrt ∘ A) (Real.sqrt ∘ B):=by
    apply isEquivalent_of_tendsto_one; have ht:=Real.continuous_sqrt.continuousAt.tendsto.comp ((isEquivalent_iff_tendsto_one ((h.eventually_gt_atTop 0).mono fun _ h=>h.ne')).1 p); rw [Real.sqrt_one] at ht; refine ht.congr' (( (tends h p).eventually_gt_atTop 0 ).mono fun i hi=>?_); exact Real.sqrt_div hi.le _
lemma mark_tie : IsEquivalent L (mark A) (mark B):= (sqrt_tie h p).inv
lemma boil_tie : ∀ᶠ i in L, |Perch.boil (A i)-Perch.boil (B i)|≤ 3*(Perch.y ( B i)):= by
    let v:= log_tie ( y_rise h ) ( spread_tie h p); have hy:Tendsto ( fun i=> |Perch.y (A i)- Perch.y (B i)|) L (𝓝 0):=by simpa only [abs_zero] using! v.abs
    filter_upwards [hy.eventually (ge_mem_nhds zero_lt_one),(Perch.y_rate.comp h).eventually_ge_atTop 1] with i hi hv; apply abs_le.mpr; have ⟨hx,h'⟩:= abs_le.mp hi; change 1 ≤ Perch.y ( B i ) at hv; unfold boil; constructor <;> nlinarith
lemma bill_tie (x:ℝ)(d:ℕ)(hp:3*|x|≤d): ∀ᶠ i in L, Perch.bill x (A i)≤ (Spread B i)^d * Perch.bill x (B i):=by
    filter_upwards [boil_tie h p,(Perch.y_rate.comp h).eventually_ge_atTop 0,(y_rise h).eventually_gt_atTop 0] with i hi hx hz; unfold Perch.bill; rw [show (Spread B i)^d= _ from (show (Spread B i)^d= Real.exp ( (d:ℝ) * Perch.y ( B i )) from by rw [exp_nat_mul,show Perch.y ( B i )= Real.log (Spread B i) from rfl,exp_log hz]),←Real.exp_add]
    apply exp_le_exp.mpr; have h := mul_le_mul_of_nonneg_right hi (abs_nonneg x); have hv:= mul_le_mul_of_nonneg_right hp hx; have he: (boil (A i) - boil (B i)) * x ≤ 3*y ( B i ) * |x| := (le_abs_self _).trans (by rw [abs_mul]; exact h); simp only[Function.comp_apply] at hv; linarith only [he,hv]
lemma markS (x:ℝ): Wage L (Spread B) (fun i=> Perch.bill x ( B i)) (fun i=> Perch.bill x ( A i)):=by
    let d:ℕ:= Nat.ceil ( 3*|x| ); let hX:=bill_tie h p x d (Nat.le_ceil _); exact ⟨d,IsBigO.of_bound' (hX.mono fun i hi=>by rw [Real.norm_of_nonneg (hedge _ _|>.le)]; exact hi.trans (le_abs_self _))⟩
omit p
lemma polyTo (n:ℕ): (fun i=> (Spread B i)^n)=O[L] (dollar B):=by
    have hx:=daybreak h n; refine IsBigO.of_bound' (?_); filter_upwards [ ( y_rise h|>.eventually_ge_atTop 1 ), hx.eventually (ge_mem_nhds zero_lt_one)] with i hi hZ
    let C:= cent B i; let U:= dollar B i; have ht: 0<C:= hedge ..; have hU:1≤U:= dollar_ge ..; have hT:C≤1:= by apply exp_le_one_iff.mpr; exact mul_nonpos_of_nonneg_of_nonpos (boil_pos _) (by norm_num)
    have hv: U⁻¹=C*C:= penny ..; apply le_trans _ ( le_abs_self (dollar B i) ); rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hi) _)];
    calc _ ≤ C⁻¹:= by rw [← one_div,le_div_iff₀ ht]; exact hZ
         _ ≤ U:= by rw [← inv_inv U,hv]; exact inv_anti₀ (mul_pos ht ht) (mul_le_of_le_one_right ht.le hT) -- can loop
lemma polyCost : Spread B =O[L] dollar B:= by simpa only [pow_one] using polyTo h 1
lemma power_age (n:ℕ) : ( ((dollar B)^n) * (mark B))=o[L] (1:ι→ℝ):= (isLittleO_const_iff (show (1:ℝ)≠0 from one_ne_zero)).mpr ((mark_sold h n).congr fun i=>by simp)
lemma fee_Θ (A:Levels G)(p:G.Simple){j:ι→ℕ} (hQ:IsEquivalent L (fun i=> A.clock.hatBeta (j i)) B) : Tendsto j L atTop:=by
    let ht:= tends h hQ; apply tendsto_atTop.mpr; intro k; filter_upwards [ht.eventually_gt_atTop ( A.clock.hatBeta k )] with i hi; by_contra! hs; exact (not_lt.mpr (hat_monoM A p hs.le)) hi
variable {j N m k:ι→ℕ}
abbrev Epoch (L:Filter ι)(B:ι→ℝ)(A:Levels G)(j:ι→ℕ):= IsEquivalent L (A.clock.hatBeta ∘ j) B
variable (C:Family G)(g:G.Simple)(m₀: C.Makes)
-- time on reparameterized indices.The witness j may vary by lifted Vane. History.β
include g
lemma Epoch.leaving (p:Epoch L B C.path.levels j): Tendsto j L atTop:= fee_Θ h C.path.levels g p
include m₀
lemma cutExposure (p:Epoch L B C.path.levels j)(k:ι→ℕ)(v:∀ᶠ i in L,j i≤ N i): IsEquivalent L (fun i=> C.path.β (N i) (k i) (j i) ) B:=by
    let H:= C.path; let Y:= H.levels; let P':= Y.clock; let T(i):= P'.hatBeta (j i); let D(i):= H.β (N i) (k i) (j i); have Ht:Tendsto T L atTop:= tends h p
    have ht: IsLittleO L ( D - T ) T:=by
       refine IsLittleO.of_bound (fun (c:ℝ) (hc:0<c)=>?_); filter_upwards [v, ( Epoch.leaving h C g p).eventually (m₀.wilson.running (c*G.slopeConstant) (mul_pos hc (slopeConstant_pos g)))] with i hi hy
       rw [Real.norm_eq_abs (T i), abs_of_pos (zero_lt_one.trans (Y.fits.delayed (j i)))]; change |D i-T i|≤ _; refine (hy (N i) (k i) hi).trans ?_; change _ ≤ c*(P'.bar+_); rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left P'.bar_pos.le) hc.le
    exact ht.isEquivalent.trans p
end YM.SignedWilsonExpansion.Purchases.UVClock
