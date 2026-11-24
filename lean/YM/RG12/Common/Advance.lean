import YM.RG12.Common.Tour
import YM.Pert.Dense.Canopy
/-!
# The paid old windows can cover every capture cut to within a factor polynomial in the log
capture scale. Not by taking subsequences/repairing fare, just purchasing the rank receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Commission
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak
open scoped Topology BigOperators
variable {G:Gauge}{p:Sheet G}{w:Rolls p}{θ:Protection w}{D:Delays θ}{B:Bar D}
open Pert.Dense
private lemma pre_up (B:Bar D)(H:G.Simple): Tendsto (preHat B) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos H))
local notation "λ!"=>G.slopeConstant
private lemma pre_term (B:Bar D)(H:G.Simple): Tendsto (fun x=>Real.log (preHat B x)/x) atTop (𝓝 0):=by
   have h:Tendsto (fun x=>preHat B x /x) atTop (𝓝 λ!):=by
      have he := (tendsto_const_nhds (x:=B.value)).div_atTop (tendsto_id (x:=atTop) : Tendsto (fun x:ℝ=>x) _ _); have ht:= he.add_const λ!; rw [zero_add] at ht
      exact ht.congr' ((eventually_ne_atTop 0).mono (fun x hx=> Eq.symm (by unfold preHat;  simp only [id_eq]; field_simp)))
   have hX:= (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (pre_up B H)).mul h; rw [zero_mul] at hX
   exact hX.congr' (((pre_up B H).eventually (eventually_ne_atTop _)).mono (fun x hx=> by change Real.log _ / (preHat B x)*(preHat B x/x)= _; field_simp))
local notation "lim0"=> Real.log
def wide (w : Rolls p)(j:ℕ):= lim0 ((w.L j).val:ℝ)
lemma wide_pos (w:Rolls p)(j:ℕ):0<wide w j:=Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 3) (show (3:ℝ)  ≤  (w.L j).val from by exact_mod_cast (w.large j).size))
-- inflated station wait: guarantee good end of stage even when testing at a setup following run center.
def trial(j:ℕ)(s:ℝ):= Nat.ceil (2*lim0 (preHat B s)/(wide w j))
lemma trial_cost (H:G.Simple)(j:ℕ): Tendsto (fun s:ℝ=> (trial (B:=B) j s:ℝ)/s) atTop (𝓝 0):=by
   have h := ((pre_term B H).const_mul 2).div_const (wide w j); rw [mul_zero,zero_div] at h
   have hv : Tendsto (fun s=> (2*lim0 (preHat B s)/wide w j)/s) atTop (𝓝 0):=h.congr fun s=>by field_simp
   -- ceil_cost private
   apply squeeze_zero' (g:=fun s => (2*lim0 (preHat B s)/wide w j)/s+1/s)
   · filter_upwards [eventually_gt_atTop (0:ℝ)] with i hi; positivity
   · filter_upwards [eventually_gt_atTop (0:ℝ), (pre_up B H).eventually_ge_atTop 1] with i hi hx; rw [← add_div]; exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg zero_le_two (Real.log_nonneg hx)) (wide_pos _ j).le)).le hi.le
   simpa only [add_zero,id_eq] using hv.add (tendsto_const_nhds.div_atTop (tendsto_id (x:=atTop) : Tendsto (fun x:ℝ=>x) _ _))
structure Bound (W : Wait B) (j:ℕ) (s:ℝ):Prop where
   space : 0 < s
   early :  W.readyHere j  ≤  s
   paid (x) : s  ≤  x → ↑(W.window j x) * wide w j  ≤  lim0 (preHat B x)
   big (x) : s  ≤  x → lim0 (preHat B x)  ≤  x/2
   theory : 2  ≤  preHat B s
lemma allowed (H:G.Simple)(W: Wait B)(h:Early W)(j:ℕ): ∀ᶠ s in atTop,Bound W j s:=by
   have hp : ∀ᶠ s in atTop, (W.window j s :ℝ)* wide w j  ≤  lim0 (preHat B s)∧ lim0 (preHat B s) ≤ s/2∧2 ≤  preHat B s:=by
      filter_upwards [eventually_gt_atTop (0:ℝ), (h j).eventually (ge_mem_nhds (show 0<(wide w j)⁻¹ from inv_pos.mpr (wide_pos ..))), (pre_term B H).eventually (ge_mem_nhds (by norm_num : 0<(1/2:ℝ))), (pre_up B H).eventually_ge_atTop 2] with s hs hw he ht
      have hv:= Real.log_pos (lt_of_lt_of_le one_lt_two ht)
      rw [div_le_iff₀ hv, inv_mul_eq_div,le_div_iff₀ (wide_pos w j)] at hw
      refine ⟨hw, by have h:= (div_le_iff₀ hs).mp he; linarith,ht⟩
   obtain ⟨s,hs⟩:=eventually_atTop.mp hp
   filter_upwards [eventually_ge_atTop s, eventually_gt_atTop 0, eventually_ge_atTop (W.readyHere j)] with t ht hv hr
   exact ⟨hv,hr,fun x hx=> (hs _ (ht.trans hx)).1,fun x hx=>(hs _ (ht.trans hx)).2.1,(hs t ht).2.2⟩

lemma pre_monotone (B:Bar D)(H:G.Simple): Monotone (preHat B):=fun u v hu=>by unfold preHat; gcongr; exact (Gauge.slopeConstant_pos H).le
lemma elevated (B:Bar D)(hH:G.Simple)(s:ℝ)(hs:2 ≤ preHat B s){x:ℝ}(hx:s ≤ x)(hv:x ≤ 2*s): lim0 (preHat B x)  ≤  2*lim0 (preHat B s):=by
   have he := pre_monotone B hH
   have hz : preHat B x  ≤  2*(preHat B s):=by have h:=Gauge.slopeConstant_pos hH; have hb:= B.good; unfold preHat; nlinarith
   apply (Real.log_le_log ((lt_of_lt_of_le zero_lt_two hs).trans_le (he hx)) hz).trans
   rw [Real.log_mul (by norm_num) (ne_of_gt (zero_lt_two.trans_le hs))]; linarith [Real.log_le_log zero_lt_two hs]

-- hierarchy and prices at varying j
lemma prepared (S:Wait B) (h:Early S)(H:G.Simple)(U:Wait B) : ∃ V:Wait B, Thicker S V ∧ Thicker U V ∧ ∀ j,∀ s:ℝ,V.readyHere j  ≤  s →
   Bound S j s ∧ Bound S (j+1) s ∧ trial (B:=B) j s  ≤  V.window j s:=by
   choose v hv using fun j=> eventually_atTop.mp (allowed H S h j)
   let K(j):= max (max (v j) (v (j+1))) (max (S.readyHere j) (U.readyHere j))
   let V:Wait B:={
     readyHere:=K
     window:=fun j s => S.window j s + U.window j s + trial j s
     minLength:=max S.minLength U.minLength
     sublin j:=by simpa [add_div] using (((S.sublin j).add (U.sublin j)).add (trial_cost (B:=B) H j)) }
   refine ⟨V,⟨le_max_left ..,fun i=> (le_max_left ..).trans (le_max_right ..),fun i s=> (Nat.le_add_right (S.window i s) _).trans (Nat.le_add_right ..)⟩,⟨le_max_right ..,fun i=>(le_max_right ..).trans (le_max_right ..),fun i s=> (Nat.le_add_left (U.window i s) _).trans (Nat.le_add_right ..)⟩,fun i s hi=> ?_⟩
   have hs: v _  ≤  s∧ v (i+1)  ≤  s:=max_le_iff.mp ((max_le_iff.mp hi).1)
   exact ⟨hv i _ hs.1,hv (i+1) _ hs.2,Nat.le_add_left ..⟩

variable {C:Family G}{U V:Wait B}
section covering
variable {A : Levels G} (H:G.Simple)
lemma scale_mono (A:Levels G) : Monotone A.S.scale:= monotone_nat_of_le_succ fun i=>by rw [Schedule.scale_succ]; exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (A.S.block i).pos))
lemma march (h:Paid V A)(c d j:ℕ)(hc:c ≤ d)(hv:∀ i,c < i → i ≤ d → A.clock.J i=j):
    A.S.scale c+(d-c:ℕ)*wide w j=A.S.scale d :=by
  induction d,hc using Nat.le_induction with
  | base=> simp
  | succ i hi IH=>
    rw [Schedule.scale_succ,← IH (fun k hk hy=> hv k hk (hy.trans (Nat.le_succ _))),← A.fits.sameFactor,hv (i+1) (by omega) le_rfl, h.lengths, show i+1-c=i-c+1 from by omega]
    push_cast; unfold wide; ring
lemma remains {k c:ℕ} (j:ℕ)(h:A.clock.J k=j)(hv:A.clock.J c=j):∀ i,c ≤ i→ i ≤ k → A.clock.J i=j:=fun _ hi hx=> le_antisymm (h ▸ A.fits.mono hx) (hv ▸ A.fits.mono hi)
lemma reserve_go {c:ℕ}{W:ℕ}(hc: W  ≤  c):c-W+W=c:=Nat.sub_add_cancel hc
include H
lemma later (U V : Wait B)(h:Paid V A)(he:∀ j s,V.readyHere j  ≤  s → Bound U j s ∧ Bound U (j+1) s ∧ trial (B:=B) j s  ≤  V.window j s)
   {j c k:ℕ}(hx:V.readyHere j  ≤  A.S.scale c)(hv:V.window j (A.S.scale c)  ≤  c)(hr: c ≤ k)
   (hj:∀ i,c - V.window j (A.S.scale c)  ≤  i→i  ≤  c + V.window j (A.S.scale c)→ A.clock.J i=j) (hk: A.clock.J k=j):
   Interior U A k:=by
    let x:=A.S.scale k;let y:=A.S.scale c;let b:=V.window j y;let t:= U.window j x
    obtain ⟨h0,-,hI⟩:=he j y hx
    have hc: c-b ≤ k:= (Nat.sub_le ..).trans hr
    have ha i (hi:c-b ≤ i)(h':i ≤ k): A.clock.J i=j:= remains j hk (hj _ le_rfl ((Nat.sub_le ..).trans (Nat.le_add_right ..))) i hi h'
    have ht: y ≤ x:= scale_mono A hr
    have hP:t  ≤  k-(c-b):=by
      by_cases hX:x ≤ 2*y
      · have he:=elevated B H _ h0.theory ht hX; have hu: (t:ℝ)* wide w j  ≤ 2 * lim0 (preHat B y):=(h0.paid _ ht).trans he
        rw [← le_div_iff₀ (wide_pos w j)] at hu; have hl:t  ≤  b:= (show t  ≤  trial (B:=B) j y from by exact_mod_cast (show (t:ℝ)  ≤  trial (B:=B) j y from hu.trans (Nat.le_ceil _))).trans hI
        have : b ≤ c:=hv; omega
      have hy : (t:ℝ)* wide w j  ≤  x/2:= (h0.paid _ ht).trans (h0.big _ ht)
      have he: y + ((k-c:ℕ):ℝ)*wide w j=x:= march h c k j hr (fun i hi hx=>ha i ((Nat.sub_le ..).trans hi.le) hx)
      have hw: (t:ℝ)*wide w j  ≤  ((k-c:ℕ):ℝ)*wide w j:=by linarith
      have hx : t  ≤  k-c:= by exact_mod_cast (le_of_mul_le_mul_right hw (wide_pos ..))
      exact hx.trans (Nat.sub_le_sub_left (Nat.sub_le ..) _)
    refine ⟨?_,?_,?_⟩
    · rw [hk]; exact h0.early.trans ht
    · rw [hk]; exact hP.trans (Nat.sub_le ..)
    rw [hk]; intro i hi h'; exact ha i (by change k-t  ≤  i at hi; omega) h'
-- choose last of earlier stage. can even require asymptotic logStep ≤ logBar, no stage-gap hypotheses
open Pert.Dense
omit H in
lemma old (h:Paid V A) {k j : ℕ}(ht : A.clock.J k = j+1)(hJ : p.first ≤ j): ∃ d<k,A.clock.J d=j ∧ ∀ i,d < i → i≤k → A.clock.J i=j+1:=by
   classical
   have hx : ∃ i,A.clock.J i ≥ j+1:=⟨k,ht.ge⟩
   let u:= Nat.find hx
   have hu:u ≤ k:= Nat.find_min' hx ht.ge
   have he : j+1 ≤ A.clock.J u := Nat.find_spec hx
   have hi:0<u:=by
      by_contra! hk; have :u=0:=by omega
      rw [this,h.firstZero] at he; omega
   have hA:u-1+1=u:=by omega
   have h0 : A.clock.J (u-1)=j:=by
      have hx : ¬( j+1 ≤ A.clock.J (u-1)):=Nat.find_min hx (show u-1< u by omega)
      have ht:= A.fits.stepSlow (u-1); rw [hA] at ht; omega
   exact ⟨u-1,by omega,h0,fun i hv hh=> le_antisymm (ht ▸ A.fits.mono hh : A.clock.J i ≤ j+1) (he.trans (A.fits.mono (by omega)))⟩

/-- At all sufficiently late levels, hit an interior compra checkpoint within log(age) age.
The last old stage is literal (NOT earlier existential choice). Also preserve constant plateau
through the connector. -/
theorem every (U V : Wait B)(h:Paid V A)(he:∀ j s,V.readyHere j ≤ s → Bound U j s ∧ Bound U (j+1) s ∧ trial (B:=B) j s ≤ V.window j s) :
   ∀ᶠ k:ℕ in atTop,∃ t,t ≤ k ∧ Interior U A t ∧ A.clock.J k ≤ A.clock.J t+1∧
     (∀ i,t< i → i ≤ k → A.clock.J i=A.clock.J k) ∧ ((k-t:ℕ):ℝ)*wide w (A.clock.J k) ≤ lim0 (preHat B (A.S.scale k)):=by
   filter_upwards [A.fits.deep.eventually_gt_atTop p.first,eventually_gt_atTop (0:ℕ)] with k hk hx
   let j:= A.clock.J k-1
   have hj:A.clock.J k=j+1:=by unfold j; omega
   have hJ:p.first≤j:=by omega
   obtain ⟨d,hd,hh,Hh⟩:=old h hj hJ
   obtain ⟨c,h1,h2,h3⟩:= h.run j hJ
   let x:= A.S.scale k;let y:=A.S.scale c; let v:= V.window j y
   have hc:A.clock.J c=j:=h3 c (Nat.sub_le ..) (Nat.le_add_right ..)
   have hC:c<k:= by
      by_contra! he; have h:= A.fits.mono he; rw [hj,hc] at h; omega
   obtain ⟨hA,hQ,-⟩:=he j y h1
   have hY:y ≤ x:= scale_mono A hC.le
   have hz : c ≤ d:=by
      by_contra! hi; have hq:=Hh _ hi hC.le; omega
   let s:=U.window (j+1) x; have hp:0<wide w (j+1):=wide_pos ..
   have ht : (s:ℝ)*wide w (j+1) ≤ lim0 (preHat B x):= hQ.paid x hY
   rcases lt_or_ge s (k-d) with hf|hf
   · refine ⟨k,le_rfl,⟨hj ▸ hQ.early.trans hY, ?_,?_⟩,by omega,fun i hi hh=> by omega,?_⟩
     · rw [hj]; exact hf.le.trans (Nat.sub_le ..)
     · rw [hj]; intro i hi h; apply Hh i (by change k-s ≤ i at hi; omega) h
     rw [hj]; simp only [Nat.sub_self,Nat.cast_zero,zero_mul]; exact (mul_nonneg (Nat.cast_nonneg _) hp.le).trans ht
   exact ⟨d,hd.le,later H U V h he h1 h2 hz h3 hh,by omega,fun i hi he=> (Hh i hi he).trans hj.symm,(by rw [hj]; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hf) hp.le) ht)⟩ -- include H
local notation "clockAt" t=> A.clock.hatBeta t
-- monotone scale span engineering factor ≤ hatBeta k. quantitative
omit H in
lemma at_most {k t:ℕ}(h:Paid V A)(hn:t≤k)(hC:∀ i,t< i→ i ≤ k → A.clock.J i=A.clock.J k)(hp:((k-t:ℕ):ℝ)*wide w (A.clock.J k) ≤ lim0 (preHat B (A.S.scale k))):
   (A.S.a t)/(A.S.a k) ≤ A.clock.hatBeta k:=by
   have hv: 0 < A.clock.hatBeta k:=zero_lt_one.trans (A.fits.delayed _)
   have hz:= march h t k _ hn hC
   have he: preHat B (A.S.scale k)= A.clock.hatBeta k:=by unfold preHat Calendar.hatBeta; rw [h.bar]
   rw [he] at hp
   -- a=exp
   rw [Stock.a_log,Stock.a_log,← Real.exp_sub,← Real.exp_log hv]; exact Real.exp_monotone (by linarith only [hp,hz])
end covering
set_option maxHeartbeats 500000 in
theorem network (W:Wait B)(h:Early W)(H:G.Simple)(U:Wait B) :∃ Q:Wait B, Thicker W Q ∧ Thicker U Q ∧ ∀ A:Levels G,Paid Q A → ∃ f:ℕ→ℕ, Tendsto f atTop atTop ∧ ∀ᶠ k:ℕ in atTop,
  f k ≤ k ∧ Interior W A (f k) ∧ A.clock.J k ≤ A.clock.J (f k)+1 ∧ (∀ i,f k < i→ i ≤ k → A.clock.J i=A.clock.J k) ∧ (A.S.a (f k))/(A.S.a k) ≤ A.clock.hatBeta k:=by
    obtain ⟨Q,hQ,hV,hE⟩:=prepared W h H U
    refine ⟨Q,hQ,hV,fun A hA=> ?_⟩
    obtain ⟨N,Hq⟩:=eventually_atTop.mp (every H W Q hA hE)
    choose! f he ht hv hJ hp using fun k hk=> Hq k hk
    have hc: Tendsto f atTop atTop:= tendsto_atTop.2 fun i=> by
       filter_upwards [eventually_ge_atTop N,A.fits.deep.eventually_gt_atTop (A.clock.J i+1)] with k hk hx
       by_contra! hf; have hF:= A.fits.mono hf.le; have hK:=hv k hk; omega
    exact ⟨f,hc,(eventually_ge_atTop N).mono fun k hk=>⟨he k hk,ht k hk,hv k hk,hJ k hk,at_most hA (he k hk) (hJ k hk) (hp k hk)⟩⟩
end YM.RG12.Commission
