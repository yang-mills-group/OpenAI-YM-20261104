import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-!
# Mid & Far horizon currency. No flow statements. Plans multiple uses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}
   {Fp Q: Recount G}{u v:ℤ}
structure Gold (P:Geo I)(K:Belt I): Prop where
   paid (i: K.time): 0≤tstart i
   day (i:K.time): exp (tstart i) = K.price.length i
   quote (i:K.time): P.habitat i.1*(1+tstart i) ≤ K.price.basic i
lemma gulfG : Gold P P.Gulf:= by
    constructor; · exact fun p=> p.2.property.1
    · exact fun _=>rfl
    exact fun p=> mul_le_mul_of_nonneg_left ( add_le_add_right ( le_abs_self (tstart p) ) (1:ℝ)) (by unfold habitat; positivity)
lemma westV : Gold P P.West:= by
    constructor; · exact fun p=> le_trans ( P.room p.1 ) p.2.property
    · exact fun _=>rfl
    exact fun p=> mul_le_mul_of_nonneg_left ( add_le_add_right ( le_abs_self (tstart p) ) (1:ℝ)) (by unfold habitat; positivity)
abbrev chips (A:Belt I) (p:A.time):=exp (-eps_gain*tstart p)
section
variable (h:Gold P K)
include h
lemma phaseY : ∀ i,phaseDiff K.price i≤ chips K i:= by
   intro i; obtain hh:= h.paid i; unfold phaseDiff chips; rw [← h.day]; unfold eps_gain; rw [ ← Real.exp_nat_mul, ← Real.exp_neg ]; apply exp_monotone; norm_num; linarith
lemma partials {b:Bool}{n:ℕ}  {d:ℕ}(_hn : d ≤ n) (hx:∀ r,fig b r→ Trust b u ( Fp n ) ( Q n ) r):
    Here b b K (circle P.η Fp n) ( rateS K u ) ∧ Here b b K ( circle P.η Q n ) ( rateS K u ) ∧ Here b b K (circle P.η Fp n-circle P.η Q n) (rateS K u * chips K) := by
   let Y(k:K.time):=meet.choose (P.η k.1) (tstart k) (show tstart k∈ Set.Ici 0 from h.paid k) -- `choose` type beg? ok
   let A:= K.price; let U:= High.meet.primary; have he(k): U.length (Y k)=A.length k:= h.day k
   have hm : Bus A U Y:= by refine ⟨⟨1,zero_lt_one,1,?_⟩,1,zero_lt_one,by simpa only [ one_mul ] using (fun i=> (he i).le)⟩; intro i; rw [pow_one,one_mul]; exact le_trans (h.quote i) (by simp [ A ]) 
   let T:= rateS K u; let V:= rateS K u * chips K; have hv :nn V:= fun i=> mul_nonneg (rateC .. ) ( Real.exp_pos _|>.le );
   refine ⟨?_,?_,?_⟩; all_goals intro E _ _ w hQ hW; obtain ⟨HF,HU,HD⟩:= hx w.length hW E w hQ rfl
   all_goals
      let p := fieldDim wfield w; have hZ: ∀ i, U.length (Y i) ^ ( p-u )=A.length i^p *( T i ):= by intro i; rw [he, sub_eq_add_neg, zpow_add₀ (A.pos _).ne']
   · exact Job.ticket (P:=Y) hm HF ( Z:=U ) (paidMono fun i=> (hZ i).le ) ( pos_nn _ (rateC _ _) _ )
   · exact Job.ticket (P:=Y) hm HU ( Z:=U ) (paidMono fun i=> ( hZ i ).le ) ( pos_nn _ (rateC _ _) _ )
   refine Job.ticket ( Z:=U) (S:=A) ( P:=Y ) ( w:=fun i=> U.length i^(p-u)* Plane.rate meet eps_gain i ) hm HD (paidMono (fun i=>?_)) ( pos_nn _ hv _ ); change (U.length (Y i))^(p-u) * (chips K i) ≤ A.length i^p * ( T i * _ ); rw [ hZ, mul_assoc]
end
variable {K₀ K₁ U₀ U₁: Planet G I}{F X: Site G I}{A C: W→ Site G I}
-- lightweight edge.Radius.
structure Arch (K:Belt I)(B D: Planet G I)(F: Site G I)(A: W→ Site G I)(R:W→ℕ): Prop where
    main: CourseK K.price 1 (plug B)
    χ : Sheet K.price 1 ( plug D )
    states i: 0< i→ Here true true K ( F i ) ( rateS K 4 )
    first i n: Here false false K ( A i n ) (rateS K ( R i ) )
structure ArcS (K:Belt I)(A B X Y: Planet G I)(F H: Site G I)(P Q:W→ Site G I)(R:W→ℕ): Prop where
    main: CourseK K.price ( chips K ) (plug (A-X))
    χ: Sheet K.price ( chips K ) (plug ( B-Y ))
    states i: 0< i→ Here true true K ( F i-H i ) ( rateS K 4 * chips K )
    first i n: Here false false K ( P i n-Q i n ) ( rateS K ( R i ) * chips K )
variable {B: Local.Physical.Deck G}(V:LitBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(p:W→ Label B)
lemma offers (h: TaylorOK M V T)(hv: Gold P K): Arch K (constantP G I (LowP G)) ( constantP G I (PlanetL G) ) (initials P T) ( rowK V P T∘ p ) ( Label.h∘ p ) ∧ Arch K (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (rowM P M ∘p) (Label.h∘p) ∧ ArcS K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (initials P T) (approach P M) ( rowK V P T ∘p ) (rowM P M ∘ p) ( Label.h ∘ p ):= by
    let S:= K.price; have hb (n:ℕ)(he: 0< n):= partials hv ( show 1 ≤ n from he ) ( fun r hr=> h.bulk n he r hr );
    have H (i:W) (n:ℕ) := partials hv ( show 0≤ n from Nat.zero_le n ) ( fun r hr=> (h.mark ( p i|>.h ) (p i|>.item)) n ( Nat.zero_le _ ) r hr );
    have he i : 1≤K.price.length i:= hv.day i ▸ Real.one_le_exp ( hv.paid i ); have hx:= cost_D (G:=G) hv.day
    exact ⟨ ⟨CoupleY he hv.day,Mate0 he hv.day,fun i hi=>(hb i hi).1,fun i n=>( H i n).1⟩, ⟨fun i j=> polar (hx i j),hx,fun i hi=>(hb i hi).2.1,fun i n=> (H i n).2.1⟩, ⟨ submarineT he hv.day (phaseY hv),submarineP he hv.day (phaseY hv), fun i hi=> ( hb i hi).2.2, fun i n=>(H i n).2.2 ⟩ ⟩ -- types.Loop.Serge.
end YM.MS.Rake
