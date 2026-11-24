import YM.OPE.Coverage.Store

/-!
## Independent prices at many log-close physical shelves with the original cutoff provenance

The comparison tests give both weak Maxell measurements and more crude,
but now sub-*log-power*, unmixed moment upper bounds in the same bought frames,
ahead of positive-order matching. This still isn't a cumulative comparison
between those frames and one true fixed normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Spec Levy MeterTest Maxwell Next.Extract
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Order}{C:Family G}{S:Table C.book}{n:ℕ} (H:Final C F S)
set_option quotPrecheck false
local notation "mCb" => Bel C.book
private abbrev Γ(C:Family G) := Maxwell.Free.spin_free C.labels
lemma under_produced {r:ℕ→ℝ}(h:Paved C F)(he:Fine r)(N D:ℕ)(μ:ℝ)(hμ:0<μ)(ht:Services C F S):∃ Y:Stored H r D (N+1) μ,Tendsto (fun i=>Y.path i / r i) atTop (𝓝 0):=by
   let nn:=N+1
   obtain ⟨v,hF',hL',⟨c,hc,hpq,hcost⟩,hP'⟩:= h.demand nn D μ (Maxwell.table_smooth C.labels) (Γ C) hμ
   let M:=4*c+5
   let x:= mark r
   let s i:= x i+M*Real.log (1+x i)
   have hM:0≤M:=by unfold M; linarith only [hc]
   have hs:Tendsto s atTop atTop:= tendsto_atTop_mono' _ (by filter_upwards [he.2.eventually_ge_atTop 0] with i hi using (le_add_of_nonneg_right (mul_nonneg hM (Real.log_nonneg (le_add_of_nonneg_right hi))))) he.2
   obtain ⟨k,hk,hA⟩:= exist_grid C.path.levels h.stride
   let f:=k∘s; have hf:= hk.comp hs; let w:=v∘f
   have hW:= Granular.comp' f hf hF'
   have hP:Stripe w:= ⟨fun p hp=>hf.eventually (hP'.rate p hp)⟩
   have hL:Lodged F w:=by
      obtain ⟨z,c,h1,h2,h3,h4,h5,h6⟩:= hL'
      exact ⟨z∘f,fun d=>c d ∘ f,h1.comp hf,h2.comp hf,h3.comp hf,fun d=>(h4 d).comp hf,fun d i=>h5 ..,fun d i=> h6 ..⟩
   let t(i):= -Real.log (w i).r
   have hall : ∀ᶠ i in atTop, x i+Real.log (1+x i) ≤ t i ∧ t i ≤ x i +(8*c+9)*Real.log (1+x i):=by
      filter_upwards [hs.eventually hA, hf.eventually hcost, he.2.eventually_ge_atTop 0, he.2.eventually_ge_atTop M] with i hs hcost hx h₂
      let a:= C.S.scale (f i)
      change |Real.log _ + a| ≤ c * Real.log (1+a) at hcost
      change |a-s i| ≤ Real.log (1+a) ∧ Real.log (1+a) ≤ 2*Real.log (1+s i) at hs
      have hw : Real.log (1+s i) ≤ 2*Real.log (1+x i):= by
           rw [show 2*Real.log (1+x i) =Real.log (1+x i) + Real.log (1+x i) from two_mul _,← Real.log_mul (by linarith only [hx]) (by linarith only [hx])]
           apply Real.log_le_log (show 0<1+s i from add_pos_of_pos_of_nonneg one_pos (add_nonneg hx (mul_nonneg hM (Real.log_nonneg (le_add_of_nonneg_right hx)))))
           have h':= Real.log_le_self (show 0 ≤ 1+x i by linarith only [hx])
           dsimp only [s]; nlinarith only [mul_le_mul_of_nonneg_left h' hM, mul_le_mul_of_nonneg_right h₂ (show 0 ≤ 1+x i by linarith only [hx])]
      have ht :=(abs_neg (t i - a)).symm.le.trans ((show |-(t i - a)| ≤ c*Real.log (1+a) from by dsimp only [w,t,Function.comp_apply]; rw [neg_sub,sub_eq_add_neg,neg_neg,add_comm]; exact hcost))
      have hdt:= (show |t i-s i| ≤ |t i-a|+|a-s i| from by rw [show t i-s i=(t i-a)+(a-s i) by ring]; exact abs_add_le ..).trans (add_le_add ht hs.1)
      replace hdt: |t i-s i| ≤ (4*c+4)*Real.log (1+x i) := by
           refine hdt.trans ?_
           nlinarith only [mul_le_mul_of_nonneg_left (hs.2.trans (mul_le_mul_of_nonneg_left hw (show (0:ℝ) ≤2 by norm_num))) (add_nonneg hc.le zero_le_one)]
      dsimp only [s,M] at *
      constructor <;> linarith only [neg_le_of_abs_le hdt,le_abs_self (t i-(x i+(4*c+5)*Real.log (1+x i))),hdt] -- abs not min
   have hw : Close r (fun i=>(w i).r):= ⟨(fun i=>(w (i)).rad),8*c+9,by linarith only [hc],by
     filter_upwards [he.2.eventually_gt_atTop 0,hall] with i hi hh
     change |x i-t i| ≤ _
     rw [abs_of_nonpos (by linarith only [hh.1,Real.log_nonneg (show 1≤1+x i by linarith only [hi])])]
     change -(x i-_) ≤ (8*c+9)*Real.log (1+x i); linarith only [hh.2] ⟩
   have hv:=Next.UVStress.supply_wheel w hW H.room.ordered H.room.kernel.smooth H.room.cutoff H.room.generic (Maxwell.table_smooth C.labels) hμ 1 one_pos
   obtain ⟨j,hj⟩:= eventually_atTop.mp hv;let q i:=max j i; let k:=w ∘ q
   have hq : Tendsto q atTop atTop := tendsto_atTop_mono (f:=id) (g:=q) (fun i=>le_max_right ..) tendsto_id
   choose y hb hc hd hf using fun i=> YM.OPE.Levy.harvested H.room.kernel H.room.ordered (Γ C) (k i).toStation (hj (q i) (le_max_left ..))
   obtain ⟨M,V,A,B,Ha⟩:=ht.along
   have hs : RoughFactory C:=by obtain ⟨a,b,c,h⟩:=ht.purchase; exact ⟨a,b,c,h.toTableTickets⟩
   refine ⟨⟨⟨fun i=>(k i).r,y,?_,?_,hb,fun i=>hc i,fun i hi=>approach H (q:=q) hq y hd hW hμ i hi, controlling H Ha hs ht.simpleGate hL hq y hd⟩,k,Granular.comp' _ hq hW,⟨fun p hp=>hq.eventually (hP.rate p hp)⟩,hd,fun i=>rfl⟩,?_⟩
   · obtain ⟨hh,b,hb,hσ⟩:=hw
     refine ⟨fun i=>hh (q i), b,hb, ?_⟩
     filter_upwards [eventually_ge_atTop j, hσ] with i hi hσ
     change _ ≤ _
     simpa only [mark,k,q,max_eq_right hi,comp_apply] using hσ
   · exact ⟨fun i=>(k i).rad, (Exists.choose_spec (Exists.choose_spec hL)).1.comp hq⟩
   have hzero := tendsto_const_nhds (x:=(1:ℝ)) |>.div_atTop (tendsto_atTop_add_const_left _ 1 he.2)
   apply squeeze_zero' (Eventually.of_forall fun i=> (div_pos (k i|>.rad) (he.1 i)).le) _ hzero
   filter_upwards [he.2.eventually_gt_atTop 0,hall,eventually_ge_atTop j] with i hiI hh hi
   have hiEq : (k i).r = (w i).r := by dsimp only [k,comp_apply,q]; rw [max_eq_right hi] -- replace expression later
   change (k i).r / r i ≤ 1/(1+x i)
   have hR := (Real.exp_monotone (show -(t i - x i) ≤ -Real.log (1+x i) from by linarith only [hh.1]))
   rw [hiEq]
   have hx: x i= -Real.log (r i):=rfl
   have ht: t i = -Real.log (w i).r:=rfl
   nth_rw 1 [hx] at hR; rw [ht,neg_sub,show -Real.log (r i) - -Real.log (w i).r=Real.log (w i).r-Real.log (r i) by ring,Real.exp_sub,Real.exp_neg,Real.exp_log (he.1 _),Real.exp_log (w i|>.rad),Real.exp_log (by change 0<1+x i; linarith only [hiI])] at hR
   rwa [one_div]
end YM.OPE.Coverage