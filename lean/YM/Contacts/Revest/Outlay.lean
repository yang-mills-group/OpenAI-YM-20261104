import YM.Contacts.Revest.Tucks
/-! Late shooting-band arithmetic. Works with full delays (never limiting extra pre-L charges).
 Prices by outputs x not post Price.resets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Revest
open Function Filter Lattice Wilson RG Pressure Progress.DirectedRecipe PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Clock Instrument Push.AbsoluteSums Sienna Model.Province.Costing UVNext.CouplingReset ConnectedActivityE6 Blaze
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G : Gauge){F:Postage} (A:Time.Forecast F) (p:Stage)(d U L:ℝ)
namespace Outlay
abbrev potion (x:ℝ):= x^(-(1/4):ℝ)
abbrev ν (x:ℝ):ℝ := x^(-(23/20):ℝ)
abbrev brutal (p:Stage) (G:Gauge):= Time.base G p+1
-- prediction difference ≤ potion. actual input band y. T P.aff Space. holds for any K true rep Local with acquired e. Equivalent clocks post.
structure Bargain (G:Gauge)(p:Stage)(F:Postage)(A:Time.Forecast F)(x y U:ℝ) :Prop where
   sound : 1<x
   offer (E:Next.Scheduling.Exchange) (θ:ℝ) (L:ℝ)(h:0<L)(β:ℝ)(hb:inBand y β) : let t:=E.cost*F.switch Instrument.plain E.cost L θ x y (gap β); δE x/24≤t∧t ≤ t+F.bundle Instrument.plain θ x y * (plain.t x)^3 -- typename
   boot : δE x/32 + 2*ν x ≤ δE x/24
   doctor B (h:Time.Same p B) (hw:B.threshold=plain.t x)(hB:B.B=cover x) (β α q e Δ:ℝ)(hp:β∈Set.Icc (y/2) (2*y))(hu:|α| ≤ U)(hf:|q-α| ≤ potion x)(hM:e≤ Time.credit G p*δE x/4) (hc:B.threshold^2 *|Δ|≤e) :
      |β+q+Δ-β-α| ≤ 1∧ B.threshold^2* |q+Δ-α| ≤ Time.credit G p*δE x∧
      (∀ z:ℝ, |z|≤ |Δ| → β+q+z ∈ Set.Icc ((1/4:ℝ)*x) (4*x)) ∧
      ν x+( e+regularNeed G B p.clip p.width p.paths 0 e) ≤ δE x/32∧ |(β+q)-(β+q+Δ)| * x^(-(43/20):ℝ) ≤ e ∧ e+regularNeed G B p.clip p.width p.paths 0 e= brutal p G *e ∧
      ∃ m κ, softNeed G B p.clip p.width p.paths q e ≤ m ∧ Payments.Rates B.B (Real.exp (-Payments.Pairing.kGoal F y β)) (A.pair.strong y β) m κ

lemma senior {B : BudgetPoint} (q:ℝ){u v:ℝ}(h:u≤v): softNeed G B p.clip p.width p.paths q u ≤ softNeed G B p.clip p.width p.paths q v:= by
   unfold softNeed; apply add_le_add _ (mul_le_mul_of_nonneg_right ?_ (budget_pos B G p.clip p.width_pos p.paths_pos.le).2.2)
   · have he:=Residual.loss_pos G B; unfold softReset Footprint.payment Footprint.degreeIncome; have hp:0≤ 1-Real.exp (-(1:ℝ)):=sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)); gcongr
   have ht:=pair_nonneg G B; have hp:=B.threshold_pos; unfold hitNeed; gcongr
lemma enact (h:0≤d) (hU:0≤U) : ∀ᶠ x in atTop,Bargain G p F A x (x+d) U:= by
    let c:=Time.credit G p; let a(x:ℝ):=δE x; let b(x:ℝ):=c*a x; let t:=(Pressure.temp);
    have hc:0<c:=Time.credit_pos ..; have hS : Rate G 1 (-(1/2) + -(1/2) +-(1/4)) (fun x=> Pressure.temp x * Pressure.temp x * (betaF G x 1)^(-(1/4):ℝ)):= ((temp_cost G).mul (temp_cost G)).mul Rate.power
    have h'_ := contraction G 1 (a:=1) (show 0<c/4 from by positivity) hS (show -(1/2:ℝ)+ -(1/2)+ -(1/4) < -(11/10:ℝ) by norm_num) -- ctor
    have h' := contraction G 1 (a:=1) (f:=fun x=> ν (betaF G x 1)) (show 0< (1/1024:ℝ) by norm_num) Rate.power (show -(23/20:ℝ) < -(11/10:ℝ) by norm_num)
    filter_upwards [Time.cash G p A (U+1) (by linarith) d h, just_near d, similar_gap_power ((11:ℝ)/5) (3/2) (by norm_num), h'_, h', (tendsto_rpow_neg_atTop (by norm_num : 0<(1/4:ℝ))).eventually_lt_const (by norm_num : (0:ℝ)<1/4), eventually_gt_atTop (max 1 (8*(d+U+3)))] with x hQ hx hG hc' hv hM hm;
    let y:= x+d; have hz : 1<x:= lt_of_le_of_lt (le_max_left ..) hm; have hx':0<x:=zero_lt_one.trans hz; have hy:1< y:= lt_of_lt_of_le hz (by unfold y; linarith); have hd:= lt_of_le_of_lt (le_max_right ..) hm;
    have ht : plain.t x=t x:= (Time.threshold_aligned x hx').1
    have ha : a x=x^(-(11/10):ℝ):= by unfold a δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx'.le,← Real.rpow_mul hx'.le]; norm_num
    have ht' : x^(-(1/2):ℝ)≤ t x:= by
       unfold t temp; rw [Real.rpow_neg hx'.le, ← Real.sqrt_eq_rpow]; apply le_mul_of_one_le_right (by positivity); exact Real.one_le_exp (sq_nonneg _)
    rw [ownHat] at hc' hv; let r:=x^(-(11/10):ℝ); have hs:x ^(-(1/2):ℝ)>0:= Real.rpow_pos_of_pos hx' _; have hb:0<a x:= ha ▸ Real.rpow_pos_of_pos hx' _
    refine ⟨hz,fun E θ L hL β hb=>?_ , (?_ : a x/32 + 2*ν x≤ a x/24),?_⟩
    · have he:=Time.lows E F (x:=x) (θ:=θ) hL hy hb; exact ⟨he.1.trans' (by have hx:a x ≤3/2*a (x+d):= hG _ _ (same x) hx; linarith only [show δE x ≤ _ from hx]),he.2⟩ -- orient
    · linarith only [hv,hb,ha]
    intro B hB ht'' hr β α q e Δ hβ hq hα he he'
    have hp: B.threshold=t x:=ht''.trans ht; have hk :=Time.authorized G p
    have hc' : B.threshold^2 * potion x≤ (c*a x)/4:= by rw [hp,ha]; linarith only [show _* (t x*t x*potion x)< c/4*x^(-(11/10):ℝ) from hc']
    have hp':x⁻¹ ≤ B.threshold^2:= by
       rw [hp]; refine le_trans ?_ (pow_le_pow_left₀ hs.le ht' 2); rw [← Real.rpow_natCast (x^(-(1/2):ℝ)), ← Real.rpow_mul hx'.le]; norm_num; rw [Real.rpow_neg_one]
    have hu:0< x⁻¹:= inv_pos.mpr hx'; have he0:0≤ e:= (mul_nonneg (sq_nonneg _) (abs_nonneg _)).trans he'; have hA : a x≤ x⁻¹:=(by rw [ha, ← Real.rpow_neg_one x]; apply Real.rpow_le_rpow_of_exponent_le hz.le; norm_num)
    have hy': |Δ| ≤ x * e:= (inv_mul_le_iff₀ hx').mp ((mul_le_mul_of_nonneg_right hp' (abs_nonneg _)).trans he'); have hd' : |Δ| ≤1/4 := by
       have hs: δE x ≤ x⁻¹ := hA; have hc: c≤64⁻¹:= hk.1; have hh: e ≤ x⁻¹/4:=by
          refine he.trans (div_le_div_of_nonneg_right (le_trans ?_ hA) (by norm_num))
          refine mul_le_of_le_one_left hb.le (hc.trans (by norm_num))
       apply hy'.trans; exact (mul_le_mul_of_nonneg_left hh hx'.le).trans_eq (by field_simp)
    have hv'' : |q+Δ-α| ≤ |q-α| +|Δ|:=by rw [show q+Δ-α=q-α+Δ by ring]; exact abs_add_le ..
    have hC : potion x≤1/4:=hM.le;
    have hd: |q|≤U+1:= by rw [← sub_add_cancel q α]; linarith only [abs_add_le (q-α) α,hq,hα,hC]
    have hr' : regularNeed G B p.clip p.width p.paths 0 e=Time.base G p * e:=by rw [Time.table G p hB]; simp
    rw [hr']; let g:= x^(-(43/20):ℝ);
    refine ⟨by rw [show β+q+Δ-β-α=q+Δ-α by ring]; linarith, by linarith only [mul_le_mul_of_nonneg_left hv'' (sq_nonneg B.threshold),mul_le_mul_of_nonneg_left hα (sq_nonneg B.threshold),he,he',hc',show c*a x ≥0 from mul_nonneg hc.le hb.le],fun z hz=>?_,?_,?_,by unfold brutal; ring,?_⟩
    · have hQ:= abs_le.mp hd; have hv:= abs_le.mp (hz.trans hd'); obtain ⟨hw,hx⟩:= hβ; obtain ⟨hh,hs⟩:= hQ; obtain ⟨hv,ht⟩:= hv; have hd:= lt_of_le_of_lt (le_max_right ..) hm; constructor <;> linarith
    · have hv : ν x ≤ a x/1024:= by rw [ha]; linarith only [hv]; -- useful
      linarith only [he,(show e≤ _ from he),hv, mul_le_mul_of_nonneg_right hk.1 hb.le,mul_le_mul_of_nonneg_right hk.2 hb.le,mul_le_mul_of_nonneg_left he (Time.base_nonneg G p).1,hb]
    · rw [show β+q-(β+q+Δ)= -Δ by ring,abs_neg]; have h':0≤g:= (Real.rpow_pos_of_pos hx' _).le; apply (mul_le_mul_of_nonneg_right hy' h').trans; apply (mul_le_mul_of_nonneg_left (_ : g ≤ x⁻¹) (mul_nonneg hx'.le he0)).trans_eq (by field_simp); rw [← Real.rpow_neg_one x]; exact Real.rpow_le_rpow_of_exponent_le hz.le (show -(43/20:ℝ) ≤ -1 by norm_num)
    let E: Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩; have hk':inBand y β:= by obtain ⟨hb,hh⟩:=hβ; unfold y at hy; exact ⟨by dsimp [y]; linarith only [hb,hy],by dsimp [y]; linarith only [hh,hy]⟩
    obtain ⟨m,κ,hM,hK⟩:= hQ B hB hr ht''|>.2.2 E 1 one_pos q 0 β hd hk'|>.2.2|>.hard; refine ⟨m,κ,?_ , hK⟩; exact (senior G p q (he.trans (by have hb:0≤c*a x:=mul_nonneg hc.le hb.le; linarith only [hb]))).trans hM
end Outlay
end YM.Contacts.Revest
