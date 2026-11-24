import YM.IterationFour.Shore.Vault

/-!
# Finance sale of Perks

Concrete station takes on H layouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Function Filter RG Wilson Lattice Spending Address Currency
open AnalyticBridge VerifiedReset Collection Vacuum Financed Render
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{C:Family G} {L:(N p:ℕ)→ Ledger C N p} {S:Purse}{D:Set ℕ}{ν:ℝ}{r w:ℕ}
local notation "a#"=> C.path.levels
variable (T:ℕ→ℕ→ℕ→Pocket)
def bonus (L:(N p:ℕ)→ Ledger C N p)(N p i:ℕ): Pocket := {T N p i with forceEarly:= if i<N then (L N p|>.stamps i).w else 0, forceGoal:= a#.clock.forcedAllowance i* Real.sqrt (a#.clock.forcedAllowance i)}

def regularA (a:Levels G) (i:ℕ) (x:ℝ):ℝ:= Time.softCeiling G (a.params i) (|x|)* (1+((a.budget i).B:ℝ))^ (4:ℕ)*(a.budget i).threshold
lemma pricedA {I:Type*}{t:I→ℕ}{U:Filter I}{x:I→ℝ}{a:Levels G}(hg:G.Simple)(hT:Tendsto t U atTop)
    (hs:Mint.Slow a)(he:Account a t U x 0): Account a t U (fun i=> regularA a (t i) (x i)) 1:=by
  have hb: Account a t U (fun i=> ((a.budget (t i)).B:ℝ)) 0:= Account.gathered t hT (cover a hg)
  have hx:= (((Account.constant hg hT a 1).joint hg hT hb).repeatOrder hg hT 4)
  have hE:= Mint.soft_rate hg a hs hT he
  have ht: Account a t U (fun i=>(a.budget (t i)).threshold) 1 := Account.gathered t hT (thermal a hg)
  simpa using! (hE.product hx|>.product ht)
lemma priced_nn (a:Levels G) (i:ℕ) (x:ℝ): 0 ≤ regularA a i x:=
  mul_nonneg (mul_nonneg (Mint.soft_pos a i _ (abs_nonneg _)) (by positivity)) (a.budget i).threshold_pos.le
lemma regularly {a:Levels G}(i:ℕ)(α:ℝ):
    softNeed G (a.budget i) (a.params i).clip (a.params i).width (a.params i).paths α (Time.forecastE a i) ≤ regularA a i α:=by
   let V:= a.params i; let p:=a.budget i; have he:=Time.authorized G V
   have hh:0 ≤ a.clock.allowance i:=show 0 ≤ Currency.weight a (11/5) i from (weight_pos ..).le
   apply Time.soft_table G V (p:=p) ⟨rfl,rfl,rfl⟩ le_rfl (mul_nonneg (Time.credit_pos G _|>.le) hh)
   calc
    _ ≤ a.clock.allowance i := le_trans (mul_le_mul_of_nonneg_right (show Time.credit G _ ≤ 1 from he.1.trans (by norm_num)) hh) (le_of_eq (one_mul _))
    _ ≤ _ := (weight_le a i (show (2:ℝ) ≤ 11/5 by norm_num)).trans (by rw [weight_two]; exact Extension.UV.threshold_large a i) -- hg unused

def reward (L:(N p:ℕ)→ Ledger C N p) (P:(N p:ℕ)→ Plan C N p r) (φ:ℕ→ℕ→ℕ→ℝ) (N q:ℕ): Sale where
    A i:= regularA a# i (P N q|>.alpha i)
    φ:=φ N q
    total i:=regularA a# i (P N q|>.alpha i)+φ N q i+ (if i=N then 0 else regularA a# i (L N q|>.stamps i|>.alpha))
    hard i:= a#.clock.forcedAllowance i^(2:ℕ)
-- finance
variable {T}
lemma strong (hG:G.Simple) (h : Treasure L) :
    (∀ᶠ i in tenor D,(fees (bonus T L) i).forceGoal > 0) ∧ (∀ᶠ i in tenor D, (fees (bonus T L) i).forceEarly ≥ 0 ∧ (fees (bonus T L) i).forceGoal ≤ C.path.levels.clock.forcedAllowance i.level) ∧ fare a# D (fun i=> (fees (bonus T L) i).forceEarly/(fees (bonus T L) i).forceGoal) 1:=by
    let W i:= a#.clock.forcedAllowance i
    have he i:0 < W i:= Real.exp_pos _
    refine ⟨Eventually.of_forall (fun i=>mul_pos (he _) (Real.sqrt_pos.mpr (he _))),Eventually.of_forall (fun i=>⟨?_,?_⟩),fun k hk=>?_⟩
    · dsimp only [fees,bonus]; split; next hy => exact (h.sells _ _ _ hy).2.2.2.2
      exact le_rfl
    · apply mul_le_of_le_one_right (he _|>.le); apply Real.sqrt_le_one.mpr; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _|>.le) _))
    filter_upwards [(at_tail (eligible D)).eventually (force_payment a# hG k)] with i hi; dsimp only [bonus,fees]; split
    next hy=>
       have hx:= h.sells i.top i.period i.level hy
       have hH:= he i.level; have hp:= Real.sqrt_pos.mpr hH
       let v:= L i.top i.period|>.stamps i.level
       change |v.w/(W i.level*Real.sqrt (W i.level))| ≤ _
       rw [abs_of_nonneg (div_nonneg hx.2.2.2.2 (mul_nonneg hH.le hp.le))]
       apply le_trans ((div_le_iff₀ (mul_pos hH hp)).2 ?_) hi
       refine le_trans hx.2.2.2.1 ?_; rw [mul_left_comm, ← sq,Real.sq_sqrt (show 0≤a#.clock.forcedAllowance i.level from hH.le)]; change W i.level ^2 ≤ W i.level*W i.level; exact le_of_eq (sq ..)
    simp only [zero_div,abs_zero]; exact (weight_pos ..).le

variable {P : (N q:ℕ)→ Plan C N q r}{hG:G.Simple}{h0:Clock.PriorNeed}{h1:Clock.DelayNeed}
/-- Only remaining postL booking inputs for Stamp on this prescription.
    Marked prices (postL units) and qlocal proof, Startup cut-room, Fk
    reserved widths before L, geometry where querying etc still separate. -/
structure Card (C:Family G) (hG:G.Simple) (T : ℕ→ℕ→ℕ→Pocket) (D:Set ℕ) (S:Purse) (P : (N q:ℕ)→ Plan C N q r) (ν:ℝ)(w:ℕ):Prop where
    terms : fare C.path.levels D (modelCharge P) 0
    alpha : fare C.path.levels D (fun i=> (P i.top i.period).alpha i.level) 0
    forecasts : ∀ᶠ (i : Address) in tenor D,
      permits ((P i.top i.period).layers i.level) (C.path.levels.budget i.level) ∧
      ∀ w':Piece G (C.side i.level i.period), w'∈ (P i.top i.period).layers i.level→w'.rank ≤ w
    printed : fare C.path.levels D (fun i=> unitBill ((P i.top i.period).layers i.level) (B C.path.levels i.level)) 3
    funds : fare C.path.levels D (fun i=> (fees T i).single) ν
    older : fare C.path.levels D (fun i=> (fees T i).response) 0
    gains : ∀ᶠ i in tenor D, (2+adjusting C.path.levels i.level)*(fees T i).repeatCost ≤ S.theta

lemma opening (he : Mint.Slow a#) (hR : UVExtension.Oasis.Floral (hG:=hG) C)
    (hm:Treasure L)(h : Card C hG T D S P ν w) : Booking (bonus T L) hG D S P ν w:=by
   have ht:= strong (D:=D) (T:=T) hG hm
   exact ⟨hR,he,ht.1,ht.2.1,ht.2.2,h.terms,h.alpha,h.forecasts,h.printed,h.funds,h.older,h.gains⟩
lemma receives (hp: Clock.Register a# h0 h1) (hG:G.Simple)(h : Treasure L) :
    fare a# D (fun i=> if i.level = i.top then 0 else (L i.top i.period|>.stamps i.level|>.alpha)) 0:=by
  let a:=C.path.levels
  let g u:= Clock.doubleLog a (Address.level u)
  have hτ:= Spending.Account.gathered _ (Financed.warm D) (Clock.smallDouble a hG)
  have hz : Account a Address.level (Financed.tenor D) (fun u=> (G.slopeConstant+1)*g u) 0:= by
    simpa only [zero_add] using! ((Account.constant hG (Financed.warm D) a (G.slopeConstant+1)).product hτ)
  apply hz.relax; filter_upwards [bright D] with i hi; split; · rw [abs_zero]; exact abs_nonneg _
  next hN =>
    obtain ⟨_,hh⟩:=hi
    let β:=(L i.top i.period|>.stamps i.level|>.alpha)
    let ℓ:= Real.log (a.S.block i.level).val
    have hV:= (h.sells i.top i.period i.level (lt_of_le_of_ne hh hN)).2.1
    have hF : ℓ ≤ g i:= (Real.log_le_self (Nat.cast_nonneg _)).trans (hp.complete i.level).2
    have hl:0 ≤ ℓ:= Real.log_nonneg (Kinetic.block_one_le ..)
    apply le_trans ?_ (le_abs_self _)
    change |β| ≤ (G.slopeConstant+1)*g i
    have hq:= abs_sub_abs_le_abs_sub β (β + G.slopeConstant*ℓ)
    rw [show β-(β+G.slopeConstant*ℓ)=- (G.slopeConstant*ℓ) by ring, abs_neg,abs_of_nonneg (mul_nonneg (G.slopeConstant_pos hG).le hl)] at hq
    linarith only [hq,hV,hF,HistoryTest.priced a i.level,mul_le_mul_of_nonneg_left hF (G.slopeConstant_pos hG|>.le)]
variable {φ:ℕ→ℕ→ℕ→ℝ}{ζ:ℝ}
lemma payments (he : Mint.Slow a#) (hm:Treasure L)(h : Card C hG T D S P ν w) (hz:ζ ≤ 1)
    (hp: Clock.Register a# h0 h1) (hφ:fare a# D (fun i=>φ i.top i.period i.level) ζ):
    fare a# D (fun i=> (reward L P φ i.top i.period).total i.level) ζ:=by
  let I (i:Address):= L i.top i.period|>.stamps i.level
  let f i:= if i.level=i.top then 0 else (I i).alpha
  let v (i:Address):=if i.level=i.top then 0 else regularA a# i.level (I i).alpha
  have hx:Account a# level (tenor D) v 1:=by
     refine (pricedA (x:=f) hG (warm _) he (receives hp hG hm)).relax (Eventually.of_forall (fun i=>?_))
     unfold f v; split; · rw [abs_zero]; exact abs_nonneg _
     exact le_rfl
  exact (((pricedA hG (warm _) he h.alpha).lower hz).joint hG (warm _) hφ).joint hG (warm _) (hx.lower hz)
lemma sunset (H:C.Makes)(he : Mint.Slow a#) (hR : UVExtension.Oasis.Floral (hG:=hG) C)
    (hm:Treasure L)(h : Card C hG T D S P ν w)(hS:11/5 < S.sigma)(hp:S.sigma<ν)(hu:S.sigma<S.w)
    (hζ:0<ζ) (hz:ζ ≤ 1)(hc:fare a# D (fun i=>φ i.top i.period i.level) ζ)(hf:∀ i∈D,∀ N j,0 ≤ φ N i j):
    ∀ᶠ i:ℕ in atTop,∀ N p,p∈D → i ≤ N→ Perks (P N p) S (bonus T L N p) (L N p) (reward L P φ N p) i:=by
  let a:= a#
  have hB:= opening he hR hm h
  let b(i:Address):= bonus T L i.top i.period i.level; let k i:= (a.budget (Address.level i)).B
  let A(i:Address):= reward L P φ i.top (Address.period i)
  let v i:= (A i).A i.level
  have hv:Account a level (tenor D) v 1:= pricedA hG (warm _) hB.slow hB.reset_alpha
  let f i:=(b i).forceEarly/(b i).forceGoal; let y i:= (k i+k i+1:ℕ)^4*(f i+2*(v i+(A i).φ i.level))
  have hx: Account a level (tenor D) y ζ:=by
     have hh:Account a level (tenor D) (fun i=> ((k i:ℕ):ℝ)) 0:= Account.gathered _ (warm _) (cover a hG)
     have hx:Account a level (tenor D) (fun i=> (((k i+k i+1:ℕ)^4:ℕ):ℝ)) 0:=by
        simpa using! (((hh.joint hG (warm _) hh).joint hG (warm _) (Account.constant hG (warm D) a 1)).repeatOrder hG (warm _) 4)
     have hz:= hx.product ((hB.masks.lower hz).joint hG (warm _) (show fare a D (fun i=> 2*(v i+(A i).φ i.level)) ζ from zero_add ζ ▸ Account.product (Account.constant hG (warm D) a 2) ((hv.lower hz).joint hG (warm _) hc)))
     simpa only [y,zero_add,b,f,fees,Nat.cast_pow] using! hz
  obtain ⟨j₀,hj⟩:= eventually_atTop.1 ((pass_iff _ _).1 (Vacuum.Financed.charter hB hS hp hu H))
  obtain ⟨j₁,hk⟩:= eventually_atTop.1 ((pass_iff (eligible D) _).1 ((hB.demand.and hB.entries).and (hx.vanishing hG (warm _) hζ (1/4) (by norm_num))))
  filter_upwards [eventually_ge_atTop j₀,eventually_ge_atTop j₁] with i h₀ h₁ N p hD hN
  have he(j)(hi:i ≤ j)(hj':j<N) := hj j (h₀.trans hi) N p ⟨hD,hj'.le⟩
  let F:= reward L P φ N p
  let t:= bonus T L N p; let R:= P N p
  change Perks _ _ _ _ F i; refine ⟨he,fun j hi hj x h=>?_,fun j hi hj=>?_,fun j hi hj=>?_,fun j _ hj=> (hm.sells _ _ _ hj).2.2.1⟩
  · let y:=(t j).due (S.limit a (j+1)) (S.guardBill a (j+1))
    have hL := (Vacuum.limits R S hG (he j hi hj) (S.limit a (j+1)) (S.limit_pos ..|>.le) le_rfl).1
    -- use room's supplies to bound ≤ allowance, enough threshold.
    have hx: S.limit a j ≤ a.clock.allowance j:= (le_add_of_nonneg_right (unit_nn (R.layers j) (he j hi hj).format (WardBin.hot a j))).trans (he j hi hj).supplies
    have ht:y ≤ (a.budget j).threshold^2:= (hL.trans hx).trans ((weight_le a j (show (2:ℝ) ≤ 11/5 by norm_num)).trans (by rw [weight_two]; exact Extension.UV.threshold_large a j))
    have hh: (signal (C:=C) _ t j x) ≤ y:= add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_left h (t j|>.prices_pos.1)) _) _
    exact (Reset.brake a j hh).trans (Time.soft_table G _ ⟨rfl,rfl,rfl⟩ le_rfl ( (t j).due_nn (S.limit_pos ..|>.le) (S.guard_pos ..|>.le)) ht)
  · obtain ⟨⟨⟨hU,hK⟩,hp⟩,hL⟩:=hk j (h₁.trans hi) N p ⟨hD,hj.le⟩; exact ⟨_,Mint.send_rate a j hp hK hU (add_nonneg (priced_nn ..) (hf p hD N j)) ((le_abs_self (y ⟨N,p,j⟩)).trans hL)⟩
  have ht:=(regularly (a:=a) j (L N p|>.stamps j|>.alpha))
  unfold F Bank.price reward; dsimp only; rw [(hm.sells _ _ _ hj).1,(H.wilson.represents N p j hj.le).clip,(H.wilson.represents N p j hj.le).vac,if_neg hj.ne]; exact add_le_add_right ht _

lemma sailing (H:C.Makes)(he : Mint.Slow a#) (hR : UVExtension.Oasis.Floral (hG:=hG) C)
    (hm:Treasure L)(h : Card C hG T D S P ν w)(hS:11/5 < S.sigma)(hp:S.sigma<ν)(hu:S.sigma<S.w)
    (hζ:0<ζ) (hz:ζ ≤ 1)(hc:fare a# D (fun i=>φ i.top i.period i.level) ζ)(hf:∀ i∈D,∀ N j,0 ≤ φ N i j)
    (hK:∀ᶠ i in atTop,∀ N p,p∈D → i ≤ N→ Peak (P N p) S (bonus T L N p) (L N p) (reward L P φ N p) i):
    ∀ᶠ i in atTop,∀ N p,p∈D → i ≤ N → ∃ X, Army (P N p) S (bonus T L N p) (L N p) (reward L P φ N p) i X:=by
  obtain ⟨k,hk⟩:= eventually_atTop.1 (waves hG H S.w)
  filter_upwards [sunset H he hR hm h hS hp hu hζ hz hc hf,hK,eventually_ge_atTop k] with i hi h hh N p hD hN
  exact heard H hG (hi N p hD hN) (h N p hD hN) (fun i he _=>hk _ (hh.trans he)) hN
end YM.IterationFour.Shore
