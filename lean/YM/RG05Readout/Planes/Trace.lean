import YM.RG05Readout.Planes.Penumbra
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Quotient expenditure toward the reference, weighted by JOINT dimensions.
 Fresh direction of any smaller charge obtained at *measurement* may be followed to reference at corresponding reduced tally. Native supports aren't assumed cheapened from a coarse renewal. Reuses argument of d64 Plane applied here to this different grape/backbone.Profile. -/
variable {H:Sight C d p}{U:Emblems C d}(hv:Awake D B b d)(ht: Spine D B h b p d N H U)
structure Tint (B:ℕ→ℕ→ℝ)(C:Family G)(d m:ℕ):Prop where
   lit i : m ≤ i → sufficient C i (powerFare B d i) ∧ grow (powerFare B d (i+1)) ≤ ((C.S.block i).val:ℝ)
variable (T':Tint B C d m) (hp:b ≤ m)
local notation "q!"=> n
local notation "wm"=> powerFare B d
local notation "F"=> grow
local notation "α!"=> C.S.a
local notation "R"=> fun i (h:i ≤ N)=> (finer U h).symm
lemma backward (ht:i<N): (R i ht.le)= (R (i+1) ht).trans (U i):=by
     dsimp only; rw [Many.sumwalk U i.le_succ ht,finer_next (le_refl i),base_value];rfl
abbrev productCost (B:ℕ→ℕ→ℝ)(d i:ℕ):ℝ:= powerFare B d i*(1+grow (powerFare B d i))
def bounty (B:ℕ→ℕ→ℝ)(d j:ℕ):=∏ i∈Finset.range j,productCost B d i
local notation "Tn"=> bounty B d
lemma grows (j:ℕ) : 1 ≤ wm j ∧ 1 ≤ F (wm j)∧2*wm j ≤ productCost B d j∧ 1 ≤ productCost B d j:= by
    have he:1 ≤ wm j:=by unfold powerFare;linarith [le_max_left 1 (B d j)]
    have ht:1 ≤ F (wm j):=by unfold grow;nlinarith only [he]
    unfold productCost
    refine ⟨he,ht, (mul_comm ..|>.trans_le (mul_le_mul_of_nonneg_left (by linarith only [ht]) (zero_le_one.trans he))), one_le_mul_of_one_le_of_one_le he (by linarith only [ht])⟩
lemma bounty_head (i:ℕ): 1 ≤ Tn i:= Finset.one_le_prod fun i _=> grows i|>.2.2.2
lemma bounty_up (i:ℕ): Tn (i+1) =Tn i*productCost B d i:= Finset.prod_range_succ ..
local notation "A'"=>ΠΩ
include ht h hv hp T'
lemma flare (hx:m ≤ i)(hn:i≤N)(v:S)(he:e<d)(hy:A' v=v):
    size (R i hn v) ≤ grow (wm i)*size (A' (R i hn v)) ∧ (α! i/α! N)^(d-e) * size v ≤ (Tn N/Tn i)*size (A' (R i hn v)):=by
     induction hn using Nat.decreasingInduction with
     | self=> dsimp only; simp only [base_value, LinearEquiv.refl_symm,LinearEquiv.refl_apply,hy,div_self (C.S.a_pos _).ne',one_pow, one_mul,div_self (show Tn N≠0 from (zero_lt_one.trans_le (bounty_head N)).ne'),le_refl,and_true]; exact le_mul_of_one_le_left (size_ge _) (grows _|>.2.1) -- simp unused?
     | of_succ k hk ih=>
        obtain ⟨hv',hT⟩:= ih (hx.trans k.le_succ); let A:= wm k; let x:=R (k+1) hk v
        obtain ⟨hs,hρ⟩:= T'.lit k hx; have hχ:= Costume.earned h ht hv (hp.trans hx) hk (e:=e) 
        obtain ⟨hK,hH⟩:= hχ.orth he hs x (hv'.trans (mul_le_mul_of_nonneg_right hρ (size_ge _))); let l:ℝ:=(C.S.block k).val
        rw [show ((R k hk.le) v)=U k x from congr_arg (fun i :_≃ₗ[ℂ]_=> i v) (backward hk)]; refine ⟨hK,?_⟩; let p:= (α! (k+1))/(α! N); have hL:0< l:=by unfold l; positivity
        have heL : α! k/α! N= l*p:=by unfold p; rw [C.S.a_step]; field_simp; rfl
        have hw: Tn N/Tn (k+1) ≥ 0:=div_nonneg (zero_le_one.trans (bounty_head _)) (zero_le_one.trans (bounty_head _)); let y:= size (A' (U k x))
        have hs : l^(d-e)*size (A' x)≤ productCost B d k*y:= hH.trans (mul_le_mul_of_nonneg_right (grows _|>.2.2.1) (size_ge _))
        change (α! k/_ )^_ * _ ≤ _* y
        rw [heL, mul_pow,mul_assoc]; apply (mul_le_mul_of_nonneg_left hT (pow_pos hL _|>.le)).trans; change l^_*(Tn N/Tn (k+1) * size (A' x)) ≤_
        rw [mul_left_comm]; exact (mul_le_mul_of_nonneg_left hs hw).trans_eq (by rw [bounty_up]; have hP: 0< productCost B d k:= zero_lt_one.trans_le (grows _|>.2.2.2); field_simp)
lemma reaches (hn:m ≤ i)(hk:i ≤ N)(x:S)(he:e<d) : ∃ v:S,A' v=v∧ A' (R i hk v)=A' x:=by
    let P:=ΠΩ; let p:= P.range; let Y:=R i hk; let V:=P.rangeRestrict.comp (Y.toLinearMap.comp p.subtype)
    have htp(v:p):P v.val=v.val:=by
        rcases (show ∃ y:S,P y=v.val from v.property) with ⟨y,hy⟩; rw [←hy];exact span_low ..
    have hs: Surjective V:= LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv' => ?_)); swap
    · apply Subtype.ext; change v.val=0; apply norm_le_zero_iff.mp
      have ha:= (flare h hv ht T' hp hn hk v.val he (htp v)).2; have hy:P (Y v.val)=0:=congr_arg Subtype.val hv'; change _≤ _*size (P (Y v.val)) at ha; rw [hy,size_zero,mul_zero] at ha; exact (size_norm _).trans (nonpos_of_mul_nonpos_right ha (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _))

    obtain ⟨v,hv⟩:= hs (P.rangeRestrict x); exact ⟨v,htp v,congr_arg Subtype.val hv⟩
lemma just_sized (hn:m ≤ i)(hk:i≤N)(he:e<d)(x:S):∃ v:S, A' v=v∧ A' (R i hk (x-v))=0 ∧ size (R i hk (x-v)) ≤ (1+F (wm i))*size (R i hk x):=by
    obtain ⟨v,hv,hV⟩:= reaches h hv ht T' hp hn hk (R i hk x) he
    have hL :size (R i hk v) ≤ F (wm i) * size (A' _):= flare h ‹Awake ..› ht T' hp hn hk v he hv|>.1
    rw [hV] at hL; refine ⟨v,hv,?_,?_⟩
    · rw [map_sub,map_sub,hV,sub_self]
    rw [map_sub, add_mul,one_mul,sub_eq_add_neg]; exact (size_add ..).trans (add_le_add_right (le_trans (size_neg ..).le (hL.trans (mul_le_mul_of_nonneg_left (size_cap ..) (zero_le_one.trans (grows _|>.2.1))))) _)
-- traversing while annihilating low projection
lemma quotient_move (hm:m ≤ i)(hi:i ≤ n)(hn:n ≤ N)(x:S)(he:e<d)(hd:A' (R n hn x)=0): ∃ v:S,A' v=v ∧ A' (R i (hi.trans hn) (x-v))=0∧ (Tn i)*size (R i (hi.trans hn) (x-v)) ≤ Tn n *(α! i/α! n)^(d-(e+1))*size (R n hn x):=by
    induction hi using Nat.decreasingInduction generalizing x with
    | self=> exact ⟨0,map_zero _,by rwa [sub_zero], by rw [sub_zero,div_self (C.S.a_pos _).ne',one_pow,mul_one]⟩
    | of_succ k hk ih=>
       obtain ⟨v,hv',hz,hw⟩:= ih (hm.trans k.le_succ) x hd; obtain ⟨y,hy,hY,hq⟩:= just_sized h hv ht T' hp hm (hk.le.trans hn) he (x-v)
       let t:=R (k+1) (hk.trans_le hn) (x-v); let K:ℝ:=(C.S.block k).val; have hκ:0<K:=by unfold K; positivity
       have he':(T) t=t:= by change t - A' t=t; rw [show A' t=0 from hz,sub_zero]
       have hs: size ((R k (hk.le.trans hn)) (x-v)) ≤ wm k * (K^(d-(e+1))*size t):=by
           rw [show R k (hk.le.trans hn) (x-v)=U k t from congr_arg (fun i:_≃ₗ[ℂ]_=> i (x-v)) (backward (hk.trans_le hn))]; apply le_trans (Costume.earned h ht hv (hp.trans hm) (hk.trans_le hn) (e:=e) |>.body t); apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (grows _).1)
           let wP:= amplify d C (C.S.block k); have hv:=overhead (i:=k) t he; rw [swell_rest,he'] at hv;exact hv
       have hstep : size (R k (hk.le.trans hn) (x-v-y)) ≤ productCost B d k*K^(d-(e+1))*size t:=(hq.trans ((mul_le_mul_of_nonneg_left hs (add_nonneg zero_le_one (zero_le_one.trans (grows _|>.2.1)))).trans_eq (by unfold t productCost; ring))) -- def t
       refine ⟨v+y,by rw [map_add,hv',hy],?_,?_⟩
       · rw [← sub_sub]; exact hY
       rw [←sub_sub]; let w:=d-(e+1); change Tn k*size _≤ _; have heQ: α! k=K*α! (k+1):=by rw [C.S.a_step]; unfold K; field_simp
       refine (mul_le_mul_of_nonneg_left hstep (zero_le_one.trans (bounty_head _))).trans ?_; rw [show Tn k * (productCost B d k*K^w*size t)=K^w*(Tn (k+1)*size t) from by rw [bounty_up];ring]
       exact (mul_le_mul_of_nonneg_left hw (pow_pos hκ _|>.le)).trans_eq (by rw [heQ, mul_div_assoc, mul_pow]; unfold w; ring)

end YM.RG05Readout.Planes
