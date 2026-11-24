import YM.FVA2.O.Rough.Peak
/-!
# Early-time contraction bounds upstream
from separated internal unit shapes to a moving horizontal cap `θ`. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Clift
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{B:Deck G} {K:Booked B}{M:MS_Data G K}{P:Geo I}
def Back (P:Geo I): Belt I:= P.solar (fun i=> Set.Iic (P.θ i)) (fun _=>measurableSet_Iic) (fun _=>id)
abbrev early (P: Geo I):= (Back P).time
abbrev deckB (P:Geo I): Home (early P) I := {
    toScale:=(Back P).price, pick:=fun i=>i.1,t:=Belt.tstart,slot _:= rfl }
local notation "S0"=> deckB P
lemma early_live : liveP (deckB P) P.η:= fun i=> P.LightY _ _ _ i
abbrev bare_age (q:ℕ)(i: early P):= exp (( ( q:ℝ ) )*(Belt.tstart i - P.θ i.1))
abbrev board (P:Geo I)(i:early P)(r:ℝ)(h:r≤ Belt.tstart i): early P:= ⟨ i.1,r,h.trans ( i.2.property )⟩
variable [NormedAddCommGroup E][NormedSpace ℝ E] {p:E} {q k n:ℕ}
variable {F H:Glade G I}
lemma age_nn : nn (bare_age (P:=P) k):= fun _=> (exp_pos _).le
lemma age_at (i:early P): bare_age k i ≤ 1:= by unfold bare_age; exact exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr i.2.property))
omit [NormedSpace ℝ E] in
lemma budgetW (i:early P)(r:ℝ)(h:r≤Belt.tstart i): (deckB P).toScale.full.cheap (board P i r h) p ≤ (deckB P).toScale.full.cheap i p * (1+( Belt.tstart i -r )):= by
    let S:=(Back P).price; let T:Belt.Walk (Back P):= P.planWalk (fun i=>Set.Iic _) _ _ ( fun i=> monotone_id ); let v:= board P i r h; have hz:0≤Belt.δf i v:=sub_nonneg.mpr h; unfold Scale.full; change S.basic v*S.weight v p≤ S.basic i*S.weight i p*(1+Belt.δf i v); rw [mul_right_comm (S.basic i)]; have hB : S.basic v ≤ _:= T.cheap i v rfl hz; have hL:= T.length i v rfl hz ; apply mul_le_mul hB; · unfold Scale.weight; gcongr
    exact S.weight_pos v p|>.le; have hp:=S.one_le i; positivity
lemma momentUp (he:Velocity F H)(hv:PastPoint F)(h:taxi (deckB P) H ( bare_age q ) k)(hq:0<q) : taxi (deckB P) F ( bare_age q ) k:= by
    intro E _ _ w hw; let S:=(deckB P).toScale; let u:=pitch w; obtain ⟨C,hC,k,h⟩:= h E w hw; obtain ⟨A,hA,hB⟩:= LogTime.backward_cost (b:=q) ( E:=ℂ ) (by exact_mod_cast hq) k; refine ⟨ C*A,by positivity,k,fun i x _=>?_⟩; let t:= Belt.tstart i; let f(r:ℝ):= F i.1 (t-r) ( sail w x ); let Y(r:ℝ):= -H i.1 (t-r) ( sail w x ); let K:= C*S.full.cheap i x^k*Qbud w S ( bare_age q ) i; have hK:0≤K:= by unfold K; exact mul_nonneg (mul_nonneg hC.le (pow_nonneg ( S.full.cheap_pos (p:=x) (i:=i) trivial ).le _ )) ( pos_nn ( bare_age q ) age_nn S i );
    have hd(r:ℝ): HasDerivAt f (Y r) r:= by convert! (( he i.1 _ ( sail w x ) ).scomp r (( hasDerivAt_id' r ).const_sub t ) ) using 1; simp; rfl
    have hU(r:ℝ) (hp:0≤r): ‖Y r‖ ≤ K*LogTime.polyExp q k r:= by
        let v:= board P i (t-r) (sub_le_self _ hp); rw [show ‖Y r‖=‖Chart (sendT ( deckB P ) H) w v x‖ from norm_neg _ ]; apply le_trans ( h v x trivial ); obtain hw:= budgetW (p:=x) i (t-r) (show _ from sub_le_self _ hp); have hr : S.full.cheap v x≤ S.full.cheap i x*(1+r):= by convert hw using 2; simp [t];
        have hS : S.length v^u≤ S.length i^u := zpow_le_zpow_left₀ ( pitch_nn w ) ( S.pos _|>.le ) ( exp_le_exp.mpr (sub_le_self _ hp) ); have hτ: bare_age q v = bare_age q i*exp (-(q:ℝ)*r):= by unfold bare_age; rw [← exp_add]; congr 1; unfold Belt.tstart v; dsimp only [board]; unfold t Belt.tstart; ring
        calc
          _ ≤ C*(S.full.cheap i x * (1+r))^k * ( S.length i^u * bare_age q v ):= by
              unfold Qbud; change C*S.full.cheap v x ^k*( S.length v ^u * _)≤ _; have hz:= S.full.cheap_pos (p:=x) (i:=v) trivial; exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le hr _) hC.le) (mul_le_mul_of_nonneg_right hS (age_nn (k:=q) v)) (mul_nonneg (length_p ..) (age_nn (k:=q) v)) (by have he:=S.full.cheap_pos (p:=x) ( i:=i ) trivial; positivity )
          _ = _ := by rw [hτ,mul_pow]; unfold K LogTime.polyExp Qbud u; ring
    have hU (r:ℝ)(hp:0≤r): dist ( f 0 ) ( f r ) ≤ K*A:= by
       apply (hB 0 r K le_rfl hp hK f Y (fun r hr=> (hd r).hasDerivWithinAt ) (fun r hr=> hU r hr.1)).trans; simp [ LogTime.polyExp ]
    obtain hf : Tendsto f atTop (𝓝 0):=( hv i.1 ( sail w x ) ).comp ( show Tendsto (fun s:ℝ=> t-s) atTop atBot from by simpa [sub_eq_add_neg,Function.comp_def] using (Filter.tendsto_atBot_add_const_left (atTop:Filter ℝ) t tendsto_neg_atTop_atBot) ); obtain hx:= le_of_tendsto ( tendsto_const_nhds.dist hf ) ( (eventually_ge_atTop (0:ℝ)).mono hU ); rw [dist_zero_right, show f 0= F i.1 t (sail w x) from (by simp [f])] at hx; unfold K at hx; apply hx.trans_eq; change C*_ * _ * A= C*A*S.full.cheap i x^k* _; ring
end YM.FVA2.O.Clift
