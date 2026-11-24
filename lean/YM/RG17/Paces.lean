import YM.RG17.Mooring
/- Overshoot window ∥ rational. Use deliberately crude H^7,S. Price point probes at smaller lengths a k for smoothish evidence at r=B.radius s, while C calibration & g remain at m (NOT asserting equivalence of truncated coefficient systems). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec OPE
open SharpGram SharpGram.Allow PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
variable {G:Gauge} (C:Family G)
set_option quotPrecheck false
local notation "a"=> C.S.a
local notation "H"=> C.path.levels.clock.hatBeta
def marcher (k:ℕ):ℝ:=a k * H k^7
lemma marcher_some {r:ℝ}(hr:0<r) : ∃ k,marcher C k ≤ r:=by
   have ht : RateIs atTop C.S.scale a (-1):=⟨Eventually.of_forall (fun _=> C.S.a_pos _),(MergeProof.Ribbons.Note.note_a C.S).pitch⟩
   have hh:= ht.mul ((strength C).power 7); exact ((hh.tends (by simp) C.S.divergent).eventually (ge_mem_nhds hr)).exists

def wheel (r:ℝ) := if h:0<r then Nat.find (marcher_some C h) else 0
lemma spoke {r:ℝ}(hr:0<r): a (wheel C r)* H (wheel C r)^7 ≤ r:=show marcher C _≤_ from by rw [wheel,dif_pos hr]; exact Nat.find_spec (marcher_some C hr)
lemma turnsWheel : Tendsto (wheel C) home atTop:=by
   refine tendsto_atTop.mpr fun i=>?_; have hp k : 0 < marcher C k:=mul_pos (C.S.a_pos _) (pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed _)) _)
   filter_upwards [(eventually_all_finset (Finset.range i)).mpr (fun k _=> (nhdsWithin_le_nhds (gt_mem_nhds (hp k)) : ∀ᶠ r:ℝ in home,r < marcher C k)),positiveLength] with r hr hh
   exact le_of_not_gt fun hf=>(not_lt_of_ge (spoke C hh)) (hr _ (Finset.mem_range.mpr hf))
lemma reverseSpoke (fx:Flick C.path.levels)(h:G.Simple): ∀ᶠ r in home,r ≤ a (wheel C r)* H (wheel C r)^8:=by
   filter_upwards [positiveLength,(turnsWheel C).eventually (eventually_gt_atTop 0)] with r hr hh
   obtain ⟨i,hi⟩:= Nat.exists_eq_succ_of_ne_zero (show wheel C r ≠ 0 from Nat.ne_of_gt hh); rw [hi]
   have ht: i<Nat.find (marcher_some C hr):=by rw [wheel,dif_pos hr] at hi; rw [hi]; omega
   let k:ℝ:= (C.S.block i).val
   have hv:H i ≤ H (i+1):= WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos h).le (Nat.le_succ _); have hz:0 < H i:= zero_lt_one.trans (C.path.levels.fits.delayed i)
   have hk:k ≤ H (i+1):= (fx.grade i).trans (by linarith only [Real.log_le_sub_one_of_pos hz,hv]); have he:0<k:=by unfold k; positivity
   refine (not_le.mp (Nat.find_min (marcher_some C hr) ht)).le.trans ?_; unfold marcher
   rw [show a i=a (i+1)*k from Eq.symm (by dsimp [k]; rw [C.S.a_step]; field_simp),mul_assoc,show (8:ℕ) = 7+1 from rfl,pow_succ' (H (i.succ))]
   exact mul_le_mul_of_nonneg_left (mul_le_mul hk (pow_le_pow_left₀ hz.le hv 7) (pow_nonneg hz.le 7) (he.trans_le hk).le) (C.S.a_pos _).le
lemma opt (fx:Flick C.path.levels)(h:G.Simple): Reach C (wheel C):=by
   let p:=wheel C; let b:=C.S.scale ∘ p
   have hs:Tendsto b home atTop:=C.S.divergent.comp (turnsWheel C)
   have ht : RateIs atTop C.S.scale a (-1):=⟨Eventually.of_forall (fun _=> C.S.a_pos _),(MergeProof.Ribbons.Note.note_a C.S).pitch⟩
   have hv : RateIs home b id (-1):=by
       have hq:= (ht.mul ((strength C).power 7)).comp (turnsWheel C); simp only [mul_zero,add_zero] at hq
       have hr:= (ht.mul ((strength C).power 8)).comp (turnsWheel C); simp only [mul_zero,add_zero] at hr
       exact RateIs.of_sandwich hq (hr.pays hs) (positiveLength.mono fun r hr=>spoke C hr) (reverseSpoke C fx h) hs
   refine ⟨turnsWheel C,?_⟩; have hh:= hv.rate.neg.inv₀ (by norm_num); norm_num at hh; refine hh.congr (fun r=>?_); rw [run,div_neg];rfl

variable {C} {f:Extraction.Order}{S:Table C.book}{F:Final C f S}{L:Layout F}
local notation "K"=> wheel C
local notation "Q"=> fun r=> H (K r)
abbrev role (C:Family G)(r:ℝ):= C.S.a (wheel C r)/r
variable (Z:Ledger L)(fx:Flick C.path.levels)
local notation "T"=> role C
include Z fx
lemma closesSmaller : Tendsto (fun r=> T r / Z.g r ^ 2) home (𝓝 0):=by
   have hm:= (tollRatio (opt C fx Z.simple)).mul Z.contour; rw [mul_inv_cancel₀ (Gauge.slopeConstant_pos Z.simple).ne'] at hm
   have hr:Tendsto (fun r=> Q r*Z.g r^2) home (𝓝 1):= hm.congr' ((ageLarge.eventually_gt_atTop 0).mono fun r hr=>by change ((H _)/run r)*(_*run r)=_; field_simp)
   have hh:Tendsto Q home atTop:= (Next.Rank.Station.hat_rate C.path.levels Z.simple).comp (turnsWheel C)
   have he:= (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (hh.atTop_mul_atTop₀ <| hh.atTop_mul_atTop₀ <| hh.atTop_mul_atTop₀ <| hh.atTop_mul_atTop₀ <| hh.atTop_mul_atTop₀ hh)
   have hx: Tendsto (fun r=> 1/(Q r)^6) home (𝓝 0):=he.congr fun i=>by ring
   refine squeeze_zero' (positiveLength.mono fun r hp=> div_nonneg (div_nonneg (C.S.a_pos _).le hp.le) (pow_nonneg (Z.positive _).le _)) ?_ (by simpa only [zero_div] using hx.div hr one_ne_zero)
   filter_upwards [positiveLength] with r hr
   let b:= H (K r); let g:=Z.g r; have hu:0<b:=zero_lt_one.trans (C.path.levels.fits.delayed _); have hg :0<g:=Z.positive r
   change T r /g^2 ≤ 1/b^6/(b*g^2)
   refine le_trans (b:=1/b^7/g^2) ?_ (le_of_eq (by field_simp;try ring)); gcongr; unfold role; exact (div_le_div_iff₀ hr (pow_pos hu _)).mpr (by rw [one_mul]; exact spoke C hr)
include Z fx
lemma stretches : Tendsto T home (𝓝 0):=by
   have hx := ((closesSmaller Z fx).mul (Z.vanishes.pow 2)); simpa only [zero_mul,div_mul_cancel₀ _ (pow_ne_zero _ (Z.positive _|>.ne'))] using hx
lemma bendsPrice : Tendsto (fun r=> T r*(((C.path.levels.budget (K r)).B:ℝ)^2)) home (𝓝 0):=by
   have he:Tendsto Q home atTop:= (Next.Rank.Station.hat_rate C.path.levels Z.simple).comp (turnsWheel C)
   refine squeeze_zero' (positiveLength.mono (fun r hr=>mul_nonneg (div_nonneg (C.S.a_pos _).le hr.le) (sq_nonneg _))) (g:=fun r=>1/(Q r)) ?_ (tendsto_const_nhds.div_atTop he)
   filter_upwards [positiveLength,he.eventually_ge_atTop 3] with r hr hQ
   let B:= Q r; have hp: 0<B:= lt_of_lt_of_le (by norm_num) (show 3 ≤ B from hQ)
   have hL:= Real.log_le_sub_one_of_pos hp
   have hx:0 ≤ Real.log B:= (Real.log_nonneg (le_trans (by norm_num) (show 3≤B from hQ))); have hh : ((C.path.levels.budget (K r)).B:ℝ) ≤ B^3:=by
      refine (Nat.ceil_lt_add_one (sq_nonneg (Real.log B))).le.trans ?_; have hm:3 ≤ B:= hQ; have hu : B^2 ≤ B^3:= pow_le_pow_right₀ (by linarith) (by decide)
      nlinarith only [hm,hx,hL,hu]
   refine le_trans (b:=1/B^7*(B^3)^2) ?_ (le_of_eq (by field_simp;try ring)); gcongr
   unfold role; exact (div_le_div_iff₀ hr (pow_pos hp _)).mpr (by rw [one_mul]; exact spoke C hr)
end YM.RG17
