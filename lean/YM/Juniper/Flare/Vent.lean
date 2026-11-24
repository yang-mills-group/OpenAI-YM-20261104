import YM.Juniper.Voucher.Inbreed
/-! # Epoch meter, for buying one *additional* curtain tax. After-L escrow; still enough before tranches & strong K. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain Bright Voucher UVExtension UVExtension.Oriel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {X:Metals G} {Q: Targets X.p X.K} {D:Rolls X.p}
variable {i j m n:ℕ}{F: Protection D} {P: Expenses Q} {U:Delays F}

-- adapted UVExtension/Yard/Allowance.pulses (private)
private lemma δe (x:ℝ)(hx:0<x):δE x=x ^ (-(11/10):ℝ) := by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
private lemma pulses (L:Side) : Rate G L (-(11/10)) δE := by
  let w x := (2:ℝ)^(11/10:ℝ)* betaF G x L ^ (-(11/10:ℝ))
  have hw: Rate G L (-(11/10)) w:= Rate.power.mul_left _
  apply hw.compare
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (G.slopeConstant * Real.log L.val),Delay.shift_pos G L] with x hx hy hp
  rw [δe _ hx, abs_of_nonneg (by positivity)]; apply le_trans _ (le_abs_self _)
  let y:= betaF G x L; have h:y/2≤x:=by unfold y betaF; linarith
  change _≤ w x
  calc
    _ ≤ (y/2)^(-(11/10:ℝ)) := Real.rpow_le_rpow_of_nonpos (half_pos hp) h (by norm_num)
    _ = w x := by rw [Real.div_rpow hp.le (by norm_num),Real.rpow_neg (x:=2) (by norm_num)]; unfold w; rw [div_inv_eq_mul]; ring
section shell
local notation "μ"=> Q j i|>.halo
local notation "T"=> (Bright.trek (Q j i|>.halo) (mast j))
local notation "V"=> (X.p.profile i)
local notation "L"=> D.L j
local notation "S"=> P j i
local notation "φ"=> (fun x=> (2*rim)*(Time.credit G V *δE x))
abbrev floral (T₀:ℕ) (x a:ℝ): ℝ := a+a+∑ i : Stars, |Slide.ray i| * ((Fintype.card (Site (Trio.fence T₀ (radiusB x) i)):ℝ)*(a+a)) -- name clash with notation T
local notation "η"=> (fun x=> floral (T) x (φ x))
def Hatch (Q:Targets X.p X.K)(D:Rolls X.p)(P:Expenses Q)(j i:ℕ)(x:ℝ): Prop:=
   let b:= Q j i|>.halo; let l:= D.L j; let T₀:= Bright.trek b (mast j); let v:= X.p.profile i; let c:= (2*rim)*(Time.credit G v*δE x)
   (P j i|>.wanting)= -(7/16:ℝ) → Marlin.tithe (2*Trio.base T₀ (radiusB x))
      (Trio.lossFee G l (P j i|>.wanting) b v x+(Voucher.Need j i x D P+ Flare.floral T₀ x c)) (Time.probe v) (coverTicket T₀) ≤ betaF G x l ^(-(1/8):ℝ)
lemma climate : ∀ᶠ x in atTop, Hatch Q D P j i x:= by
   by_cases h: (P j i|>.wanting)= -(7/16:ℝ); swap; · exact Eventually.of_forall fun _ hx=> (h hx).elim
   have hv: Rate G L (-(11/10)) δE:= pulses _
   have he : Rate G L (-(11/10)) (φ):=(hv.mul_left _).mul_left _
   have hf : Rate G L (-(11/10)) η := by
      apply Rate.add (he.add he); apply Trio.sparks; intro a; simpa only [zero_add] using! (((feeStars G L T a).mul (he.add he)).mul_left _)
   have hp:= (P j i|>.wanting)
   have ht := twigs G L (S).wanting (Q j i|>.halo) V h
   have hU:= twigs G L (S).wanting T V h
   have he := ((Trio.balls G L (Trio.rows G L T|>.2.2.2)).mul (ht.add ((hU.add ht).add (hf.weaken ?_)))).mul_right (Real.exp (((V).supportExponent+1+1)*coverTicket T)) (-(1/8):ℝ) (by rw [h]; norm_num)
   swap; · rw [h]; norm_num
   filter_upwards [he] with x he; exact fun _=> (le_abs_self _).trans he
end shell
structure Vent (Q:Targets X.p X.K)(D:Rolls X.p)(P:Expenses Q){F:Protection D}(W:Delays F):Prop where
   promised (j i:ℕ) : StepStages j i → ∀ x,W.betaEntry j ≤ x → Hatch Q D P j i x
lemma snapshot : ∃ W,DelayLe U W∧Vent Q D P W := by
   obtain ⟨x,-,hv,hx⟩:= collect_upper U.betaEntry _ fun j=>eventually_transitions j _ _ (fun i (_ :StepStages j i)=> climate (Q:=Q) (P:=P) (D:=D) (i:=i) (j:=j))
   exact ⟨{U with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,⟨fun j i h x ht=> hx j x ht i h⟩⟩
open UVExtension.Lamppost Charted Dales Guild Tabernacle
variable {p:Return.Wages}{v:ℕ→ℝ}
abbrev launched (_R : PhysicalNext.Repeat.Register D P p v) (U:Delays F) := Vent Q D P U
def rebateWind (G:Gauge): Legato.Booster G where
   asks S _ _ W:= launched S W
   buy _ _ _ _:= snapshot
   mono h hv:= ⟨fun j i ht x he=> h.promised j i ht x ((hv.beta j).trans he)⟩
section pay
variable {A:Alloy X D}(R:Factor A) {N m n:ℕ}{ε β:ℝ}(H:Tour R N m n ε) (d:Cham A.B.a (m+1) n)
variable {u:Valve (m+1) n A.B.a d}(hu: Reality A.B.a (m+1) n d u β)
local notation "B"=> (A.B.a.budget m)
local notation "x"=> A.B.a.clock.hatBeta m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "B'"=> A.B.a.clock.J m
local notation "V"=> (X.p.profile B')
local notation "L"=> D.L J
local notation "f"=> (2*rim)*forecastE A.B.a m
local notation "T'"=> Bright.miner R m
local notation "F"=> (Need J B' x D R.expense+Flare.floral T' x f)
local notation "ν"=> Rain.tempe (A:=A) (Z:=R.expense) (m:=m)
local notation "K"=> Cash.armK (R.target J B') L (R.shape.μ J B') x 0 (R.expense J B').degrees
variable (h:Vent R.target D R.expense A.delay)(hv:∀ j i,(R.expense j i).wanting= -(7/16:ℝ))
include h hv H hu
lemma rising : Windy R m β F (2*Bright.home R m) n := by
   let l:=T'; let b:= β; let S:=Voucher.Need J B' x D R.expense; let c:=Flare.floral T' x f; let N:=coverTicket T'; let u':= Marlin.tithe (2*Bright.home R m) (ν+(S+c)) (B) N
   have he': (B).supportExponent=(X.p.profile B').supportExponent:= (Rain.jersey (A:=A) (m:=m)).2.2.1
   have hh:= step_paid A.B.a m; have hz:= (standing R H d hu).invested; have hb: Next.Scheduling.inBand (betaF G x L) b:=by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hu.1
   have hw:= A.B.valid.pays m; have he:u'≤betaF G x L ^(-(1/8):ℝ):= by unfold u' Marlin.tithe S c forecastE; rw [params_eq A.B.valid,he']; exact h.promised _ _ hh _ hw (hv ..)
   have hY (p:ℕ):0 ≤ Trio.lossFee G L (R.expense J B'|>.wanting) p V x:= by
    have ht:0≤ heat G L (R.expense J B'|>.wanting) p V x:= by
      unfold Trio.heat; rw [← PriceCompiler.beta_eq A.B.valid]; have h:0≤ Height.away (V):=by unfold Height.away Push.Local.turnCost; positivity
      have hl:0 < A.B.a.clock.hatBeta (m+1):= zero_lt_one.trans (A.B.a.fits.delayed _); positivity
    unfold lossFee; exact add_nonneg (add_nonneg ht ht) (sum_nonneg fun i _=> mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg ht ht)))
   have hf:0≤ f:= by unfold rim forecastE; have ht:=(fundedP m A.B.a).1; have hξ:=Time.credit_pos G (A.B.a.params m); positivity
   have hc:0≤ c:= add_nonneg (add_nonneg hf hf) (sum_nonneg fun i _=> mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hf hf)))
   have hp :0≤ ν + (S + c):= add_nonneg (hY _) (add_nonneg (add_nonneg (hY _) (hY _)) hc)
   have hP:0≤u':=by unfold u' Marlin.tithe; positivity
   have hL: 0≤ K:= budget_nonneg (hz.choose_spec.2 0)
   obtain ⟨η,hη⟩:= (R.inn.terms.allot _ _ hh _ hw).2.2.1 _ hb _ u' hL hP ((R.pledging.conducts.income.earns _ _ hh _ hw _ hb).trans_eq (by ring)) he
   refine ⟨⟨η,N,?_,fun i=>?_⟩,mul_le_mul_right (bigger R) _⟩
   · unfold forecastK; rw [PriceCompiler.beta_eq A.B.valid]; exact hη
   unfold N coverTicket; apply Nat.cast_le.mpr; exact (Trio.scaleMeters l (radiusB x) (B).B_pos i _ le_rfl).trans_eq (by rw [two_mul])
end pay
end YM.Juniper.Flare
