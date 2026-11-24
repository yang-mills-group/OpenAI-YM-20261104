import YM.OPE.Samples.Pose
/-!
# Windows and ports, independent of representative placement
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter MeasureTheory Lattice RG Wilson Polar Rhythm
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C: Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w n A:ℕ} {f:Filter L} {X:L→ I→E4}
    {T:L→ℝ}{R r s: L→ℕ→ℝ} {α:ℕ→ℝ}{q e a b : L→ℝ}{M η:ℝ} {x: I→ E4} {δ s' :ℕ→ ℝ}
set_option quotPrecheck false
local notation "β"=> C.path.levels.clock.hatBeta
local notation "μ"=> C.S.a
local notation "σ"=> (fun i=> C.path.levels.budget i)
structure BlockFrame (Q:Rhythm I)(s δ:ℕ→ℝ)(x:I→ E4)(H:ℕ) :Prop where
    pair i j:i≠j → ‖x i - x j‖ ≤ s (Q.gap i j)
    reserve i j : i≠j→ δ (Q.gap i j) < ‖x i-x j‖
    hostel : ‖x Q.star‖ ≤ s H
local notation "B!"=> Border f T Q.limit R r α
local notation "D!"=> Q.Loom
abbrev draft (Q:Rhythm I)(R r:ℕ→ℝ)(M η:ℝ)(H:ℕ)(x:I→ E4) := BlockFrame Q (fun t=>M*R t) (fun t=>η*r t) x H
lemma GapHomebound (i j:I): Q.gap i j ≤ Q.limit:= (Q.loose i j).trans (Q.bounded i)
variable (F:BlockFrame Q s' δ x H) (H':H ≤ Q.age Q.star)
namespace BlockFrame
include F
lemma dawn (he:t≤Q.limit)(hx:Q.phase t i j)(h:∀ u,t ≤ u→ u ≤ Q.limit→s' u ≤ s' t)(hp:0 ≤ s' t): ‖x i-x j‖ ≤ s' t:=by
   by_cases hc:i=j; · simp [hc,hp]
   exact (F.pair i j hc).trans (h _ ((Q.split hc).mp hx) (GapHomebound i j))
include H'
lemma whole (he:t≤Q.limit)(h:∀ u,t ≤ u→ u ≤ Q.limit→s' u ≤ s' t)(hp:0 ≤ s' t) : ‖x i-Q.point H x i t‖ ≤ 2*s' t:=by
   by_cases hc:Q.pinned H i t
   · rw [Q.lead_zero hc,sub_zero]; have hu := (F.hostel).trans (h H hc.1 (le_trans H' (Q.bounded _)))
     linarith only [hu,F.dawn he (Q.swap ((Q.on_focus).1 hc.2)) h hp,norm_sub_norm_le (x i) (x Q.star)]
   exact (F.dawn he (Q.matchs i t) h hp|>.trans (show s' t≤2*s' t by linarith only [hp])).trans_eq' (by rw [point,if_neg hc]) -- trans_eq'? order.
end BlockFrame
-- moving all grips in their layers
variable (B:Border f T Q.limit R r α)
lemma rate_pose (hG:G.Simple){T:L→ℝ}{a':ℝ} {m:L→ℕ} (hm:Height C.S f T m a')(ht:Tendsto T f atTop)(hp:a' ≤ 1) : ∀ᶠ i in f, (((C.path.levels.budget (m i)).B:ℝ)^2) ≤ T i^16:=by
    -- extend `Log/Rail.peep_cost`.
    let b i:=β (m i); let J:=G.slopeConstant; let a:= C.path.levels.clock.bar; have ha:= C.path.levels.clock.bar_pos; have hJ:= Gauge.slopeConstant_pos hG; filter_upwards [hm.pace.eventually (ge_mem_nhds (show a' < 2 from hp.trans_lt one_lt_two)), ht.eventually_ge_atTop (a+2*J), ht.eventually_ge_atTop 2] with i hi hT hv
    have hh:0<T i:= zero_lt_two.trans_le hv; have hF: b i ≤ T i^2:=by
       have he:C.S.scale (m i) ≤2*T i:= (div_le_iff₀ hh).mp hi; change a + J*C.S.scale (m i) ≤ _; nlinarith only [mul_le_mul_of_nonneg_left he hJ.le, le_mul_of_one_le_right (show 0 ≤ a from ha.le) (one_le_two.trans hv), mul_le_mul_of_nonneg_right hT hh.le]
    have hp:1 < b i:= C.path.levels.fits.delayed _; have he : ((σ (m i)).B:ℝ) ≤ T i^8 := by
       refine le_trans (Nat.ceil_lt_add_one (sq_nonneg (Real.log (b i)))|>.le) ?_; have he:Real.log (b i) ≤ T i^2:= (Real.log_le_self (zero_le_one.trans hp.le)).trans hF; have hg: (Real.log (b i))^2 ≤ (T i^2)^2:= pow_le_pow_left₀ (Real.log_nonneg hp.le) he _; have hu: (2:ℝ) ≤ T i^4:= hv.trans ((pow_one _).symm.trans_le (pow_le_pow_right₀ (one_le_two.trans hv) (by norm_num))); nlinarith only [hg,hu,sq_nonneg (T i^4 - 1)]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) he 2).trans_eq (by ring)
lemma peep (hG:G.Simple){D:L→Loom Q} {P:ℝ} (h:Oscars B P D C)(hm:t ≤ Q.limit)(he:0<η) : ∀ᶠ i in f,let j:=(D i).launch t; 2* μ j*(((σ j).B^2+2:ℕ):ℝ) ≤ η*r i t:=by
    have ht:=B.life; let q i:=(D i).launch t; filter_upwards [rate_pose hG (h.upper t hm) ht ((B.pace t hm).2), h.meter t hm, (B.rates t hm).pos, ht.eventually_ge_atTop 2,ht.eventually_gt_atTop (4/η)] with i hi hX hr hT hV
    intro j; let v:= T i; have hv':1 ≤ v:= one_le_two.trans hT; have hv:0<v:=zero_lt_one.trans_le hv'
    have hu:↑((σ j).B^2+2:ℕ) ≤ v^16+v^16:=by push_cast; exact add_le_add hi (hT.trans ((pow_one v).symm.trans_le (pow_le_pow_right₀ hv' (by norm_num))))
    apply le_trans (mul_le_mul_of_nonneg_left hu (mul_pos two_pos (C.S.a_pos _)|>.le)); apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX.le zero_le_two) (show 0≤v^16+v^16 from (by positivity))).trans
    have he: 4/η < v^16:= lt_of_lt_of_le hV ((pow_one v).symm.trans_le (pow_le_pow_right₀ hv' (by norm_num)))
    have hz := (div_lt_iff₀' ‹0<η›).mp he; exact le_trans (b:=4*r i t/v^16) (by unfold v; have hv:0<T i:=hv; apply Eq.le; field_simp; ring) ((div_le_iff₀ (pow_pos hv _)).mpr (by nlinarith only [mul_lt_mul_of_pos_left hz hr]))
-- musical variants
namespace Border
local notation "U"=> Q.localTime H
local notation "V!"=> I→ E4
variable (Q H)
def pitches (T:L→ℝ)(r:L→ℕ→ℝ)(i:L)(x:I→ E4)(j:I):= (r i (Q.localTime H j)/T i) • x j
abbrev orbit (T:L→ℝ)(r:L→ℕ→ℝ)(X:L→ I→ E4)(i:L)(x:I→ E4):= Q.moveElig H (X i) (pitches Q H T r i x)
variable {Q H}
local notation "orbit!"=> orbit Q H T r X
local notation "tick" => T
-- norm budget & class motion
include B H'
lemma advance (he:t≤Q.limit) : ∀ᶠ i in f, ∀ (x : I→ E4),‖x‖ ≤ 1 → ∀ j:I,t ≤ Q.localTime H j → ‖pitches Q H T r i x j‖≤ r i t/T i:=by
   filter_upwards [B.life.eventually_gt_atTop 0, eventually_all.mpr (fun j:I=> (B.rates (U j) ((Q.timeBirth H' j).trans (Q.bounded j))).pos),eventually_all.mpr (fun j:I=>eventually_all.mpr fun h:t ≤ U j=> B.in_order h ((Q.timeBirth H' j).trans (Q.bounded j)))] with i h hv hA x hx k hk
   unfold pitches; rw [norm_smul, Real.norm_of_nonneg (div_pos (hv k) h|>.le)]; exact (mul_le_of_le_one_right (div_pos (hv k) h|>.le) (le_trans (norm_le_pi_norm x _) hx)).trans (div_le_div_of_nonneg_right (hA k hk|>.1) h.le)
lemma spend (h:0<η): ∀ᶠ i in f, (Fintype.card I:ℝ)/T i ≤ η:=by
    refine (show Tendsto (fun i=>(Fintype.card I:ℝ)/T i) f (𝓝 0) from tendsto_const_nhds.div_atTop B.life).eventually (ge_mem_nhds h)
-- remove [NeBot] and H' for spend
lemma major (i j k:I)(x:E4): ‖Q.reaches H x j i - Q.reaches H x j k‖ ≤ ‖x‖:= by by_cases he:Q.tracked H j i <;> by_cases hh:Q.tracked H j k <;> simp [reaches, he,hh]
lemma ratioDebt (j k:I) (hp: Q.phase t j k)(η:ℝ)(he:t≤Q.limit) (hη:0<η) : ∀ᶠ i in f, ∀ (x:I→ E4),‖x‖ ≤ 1→ ‖orbit! i x j-orbit! i x k-(X i j-X i k)‖ ≤ η*r i t :=by
    let x' i t' u:= Q.reaches H (pitches Q H T r i u t') t'; filter_upwards [B.advance H' he,B.spend H' (η:=η) hη,(B.rates t he).pos,B.life.eventually_gt_atTop 0] with i hf hp' hr ht x hx; let v a j:= x' i a x j; unfold orbit moveElig; rw [show X i j+(∑ j',v j' j)-(X i k+(∑ k',v k' k))-(X i j-X i k)=(∑ j',v j' j)-(∑ k',v k' k) from (by abel),← Finset.sum_sub_distrib]
    apply le_trans (norm_sum_le ..); apply (Finset.sum_le_sum (g:=fun _=> r i t/T i) (fun u _=>?_)).trans
    · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact (show Fintype.card I*(r i t/T i)=(Fintype.card I:ℝ)/T i *r i t by ring).trans_le (mul_le_mul_of_nonneg_right hp' hr.le)
    rcases lt_or_ge (U u) t with hi|hi
    · unfold v x'; rw [Q.follow_finer _ hp hi, sub_self,norm_zero]; exact div_nonneg hr.le ht.le
    exact (major H' B j u k _).trans (hf x hx u hi)
lemma hostelFee (j:I)(hp:Q.pinned H j t)(he:t ≤ Q.limit)(hη:0<η) : ∀ᶠ i in f,∀ x:I→ E4, ‖x‖ ≤ 1→ ‖orbit! i x j-X i j‖ ≤ η*r i t:=by
    filter_upwards [B.advance H' he,B.spend H' hη,(B.rates t he).pos,B.life.eventually_gt_atTop 0] with i hf hp' hr ht x hx; unfold orbit moveElig; rw [add_sub_cancel_left]; apply le_trans (norm_sum_le ..); apply (Finset.sum_le_sum (g:=fun _=> r i t/T i) (fun u _=>?_)).trans
    · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact (show Fintype.card I*(r i t/T i)=(Fintype.card I:ℝ)/T i *r i t by ring).trans_le (mul_le_mul_of_nonneg_right hp' hr.le)
    rcases lt_or_ge (U u) t with hi|hi; · rw [Q.root_affords H' hp hi _,norm_zero]; exact div_nonneg hr.le ht.le
    unfold reaches; split; exact hf x hx u hi; rw [norm_zero]; exact div_nonneg hr.le ht.le
lemma trajectory (hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))(hη:0<η) : ∀ᶠ i in f,∀ x:I→ E4,‖x‖ ≤ 1→ draft Q (R i) (r i) (M+η/2) (η/2) H (orbit! i x):=by
    have hp(j k:I):= B.ratioDebt (X:=X) H' j k (t:=Q.gap j k) (Or.inr le_rfl) (η/2) (GapHomebound j k) (half_pos hη); have ht: H ≤ Q.limit:= H'.trans (Q.bounded _); have hh:=B.hostelFee (X:=X) H' _ (show Q.pinned H Q.star H from ⟨le_rfl,(Q.on_focus).2 (Q.yes ..)⟩) ht (half_pos hη)
    filter_upwards [hX,eventually_all.mpr (fun j=> eventually_all.mpr (hp j)),hh,(eventually_all_finset (Finset.Iic Q.limit)).mpr (fun i hi=> (B.narrow i (Finset.mem_Iic.mp hi)))] with i hi hu hf hr x hx -- adjust
    have ht'(l:ℕ)(ht:l ≤ Q.limit): (η/2)*r i l ≤ (η/2)*R i l:= mul_le_mul_of_nonneg_left (hr l (Finset.mem_Iic.mpr ht)) (half_pos hη).le
    refine ⟨fun j k hk=> ?_,fun j k hk=> ?_,?_⟩
    · linarith only [hi.pair j k hk,hu j k x hx,ht' (Q.gap j k) (GapHomebound j k), norm_sub_norm_le (orbit! i x j-orbit! i x k) (X i j-X i k)]
    · linarith only [hi.reserve j k hk,hu j k x hx,norm_sub_norm_le (X i j-X i k) (orbit! i x j-orbit! i x k),norm_sub_rev (X i j-X i k) (orbit! i x j-orbit! i x k)]
    linarith only [hi.hostel,hf x hx,ht' _ ht, norm_sub_norm_le (orbit! i x Q.star) (X i Q.star)]
end Border
end YM.OPE.Log.Trunk
