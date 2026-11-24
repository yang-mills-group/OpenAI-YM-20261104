import YM.Juniper.Bright.Boost
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {i j :ℕ}

-- numerical predicate s actual and kernel R before boost
variable {C: Targets X.p X.K} (D: Rolls X.p) {E: Expenses C}
    {p:Return.Wages}{v : ℕ→ℝ} (R:PhysicalNext.Repeat.Register D E p v) (P: PostCost D)
open Bright
local notation "J"=> (trek (C j i|>.halo) (mast j))
local notation "L"=> (D.L j)
local notation "U"=> (X.p.profile i)
-- expose constants stage any epoch via after-L properties. plume deliberately overbuys to merge more than pure later. For here EXACT stage loss.
abbrev Need (j i:ℕ)(x:ℝ) (D:Rolls X.p)(E: Expenses C):= Trio.lossFee G (D.L j) (E j i).wanting (trek (C j i|>.halo) (mast j)) (X.p.profile i) x+Trio.lossFee G (D.L j) (E j i).wanting (C j i).halo (X.p.profile i) x
def emblem (j i:ℕ)(x:ℝ) (D:Rolls X.p)(E: Expenses C): Prop:=
   let p:= X.p.profile i; let B:= Height.away p; let K:= D.L j; let T:= (E j i); let k:= (C j i).halo; let N:= trek k (mast j)
   (T.wanting= -(7/16:ℝ)) →
    Marlin.tithe (2*(Trio.base N (radiusB x))) (Trio.lossFee G K T.wanting k p x+ Need j i x D E) ⟨p.power,p.order,p.supportExponent,1,1,p.power_ge,p.order_ge,p.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicket N) ≤ betaF G x K ^ (-(1/8):ℝ) ∧
    gold G K x+B*(planks G K N p x*Real.exp (stout p*coverTicket N)) ≤ (1/4:ℝ)*(Time.credit G p*δE x)
lemma trophy {_u:ℝ} (h:0< _u):∀ᶠ x:ℝ in atTop,gold G L x+Height.away U*(Trio.planks G L J U x * Real.exp (stout U * coverTicket J))≤ _u*(Time.credit G U*δE x):=by
  have ht : Rate G L (-(23/20)) (gold G L) := Rate.power
  have hh := ht.add (((Trio.skyward G L J U).mul_right (Real.exp (stout U * coverTicket J))).mul_left (away U)); let A:= Time.credit G U
  have hp: 0<A:=Time.credit_pos ..
  filter_upwards [Sienna.contraction G L (a:=1) (b:=_u*A) (by positivity) hh (show -(23/20:ℝ)< -(11/10) by norm_num),Delay.shift_pos G L,eventually_gt_atTop (0:ℝ)] with x ht hx hX
  have he : δE (betaF G x L)=betaF G x L ^ (-(11/10):ℝ):= by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
  have hh : δE (betaF G x L) ≤ δE x:= by
    unfold δE; refine Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num); exact inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt (show x ≤ betaF G x L from le_add_of_nonneg_right (Work.E04.shift_nonneg G L)))
  rw [one_mul,← he] at ht; exact ht.le.trans ((mul_le_mul_of_nonneg_left hh (by positivity : 0≤_u*A)).trans_eq (mul_assoc ..)) -- specialization adapted compar
lemma cap_rates : ∀ᶠ x in atTop, emblem j i x D E:= by
   by_cases h: (E j i).wanting= -(7/16:ℝ); swap; · exact Eventually.of_forall fun x hx=> (h hx).elim
   have hz:=twigs G L (E j i|>.wanting) (C j i|>.halo) U h
   have he := ((Trio.balls G L (Trio.rows G L J|>.2.2.2)).mul (hz.add ((twigs G L ((E j i).wanting) J U h).add hz))).mul_right (Real.exp (((U).supportExponent+1+1)*coverTicket J)) (-(1/8):ℝ) (by rw [h]; norm_num)
   filter_upwards [he,trophy (C:=C) (i:=i) (j:=j) D (show 0<(1/4:ℝ) by norm_num)] with x hx hv; exact fun _=> ⟨(le_abs_self _).trans hx,hv⟩
variable {H: Protection D}
structure Moat (W:Delays H):Prop where
   veil (j i:ℕ) : StepStages j i→∀ x,W.betaEntry j ≤ x → emblem j i x D E
lemma issue (W : Delays H) : ∃ V, DelayLe W V ∧ Moat D (E:=E) V:= by
   obtain ⟨x,-,hv,hx⟩:= collect_upper W.betaEntry _ fun j=>eventually_transitions j _ _ (fun i (_ :StepStages j i)=> cap_rates D (j:=j) (i:=i) (E:=E)); exact ⟨{W with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,⟨fun j i h x ht=> hx j x ht i h⟩⟩
abbrev passed (_r:PhysicalNext.Repeat.Register D E p v) (W:Delays H):= Moat D (E:=E) W
def purchase (G:Gauge) : Legato.Booster G where
   asks S _ _ W:= passed _ S W -- infer Expenses from S
   mono h hv:= ⟨fun i j hT x hx=> h.veil i j hT x ((hv.beta _).trans hx)⟩
   buy _ _ _ W:= Voucher.issue _ W
end YM.Juniper.Voucher
