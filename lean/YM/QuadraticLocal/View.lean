import YM.QuadraticLocal.Tides
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Little
/-!
Forecast vs stage reserve for marked after same re-expression & coupling path.

`Ticket.Coming`, `Ticket.Waiting` determined BEFORE unmarked trajectory selection (for ALL
later input Budgets). Using Eyes reserve to pay ANY post normalized positivity etc,
reg fees at ﬁled budget ≤ y^δ where δ=~1/stage; operator receipts.
Here relative mark uncertainty cost for any inverse power loaded coarser strong share (even
if r/κ in uncertain kinetic). Can give caps before iterative portion of adjacent step proof.
Mark masses accounted separately. Can strengthen post delay with any assumptions for actual
trajectory bind. Distinct hit and exponent re-expression.Walk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Beaming
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums Mallow Blush PriceCompiler
open ThroughLaunch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
variable {G: Gauge}
-- book ℝ choose height before-L. Also forecasts Budget Flow shrinks. Extra.Every.Clock.
section sheets
variable {P:Teller G} (V:ConnectedActivityE6.Target G P)
variable (K : Postage) (L:Side) (m:ℝ)
local notation "Θ"=> Instrument.plain
local notation "βF"=> fun x=> betaF G x L
lemma divided {G : Gauge} (r:ℝ): ∀ᶠ x:ℝ in atTop,∀ β, Next.Scheduling.inBand (betaF G x L) β→ Real.exp (-Pairing.kGoal K (betaF G x L) β) ≤ (betaF G x L)^ r * (Blush.glyph x) := by
   let v : ℝ:= K.rate/4; let c:= G.slopeConstant*Real.log (L.val:ℝ); have hx:0<v:= div_pos K.pos (by norm_num)
   filter_upwards [Time.late_force v c hx, (Blush.efferv (t:=K.rate) (G:=G) (L:=L) K.pos (r-1)) r (sub_one_lt _)] with x he ht β hb
   let y:= betaF G x L; let g:= Blush.glyph x; let a:=(Instrument.plain.P y);
   have hp : Real.exp (-Pairing.kGoal K y β) ≤ Real.exp (-v*a^2):= (he K le_rfl β hb).1
   have hu : straw K.rate L G x=2*Real.exp (-v*(1/4)*a^2):= by
      rw [show a=Delay.fineMonitor G L x from Clock.watch_two y]
      rfl
   have hh:Real.exp (-v*a^2) ≤ straw K.rate L G x:= by rw [hu]; refine (Real.exp_monotone ?_).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (by norm_num)); linarith only [mul_nonneg hx.le (sq_nonneg a)]
   exact hp.trans (hh.trans ((div_le_iff₀ (Blush.glyphpos x)).1 (by rw [div_eq_inv_mul]; exact (le_abs_self _).trans ht)))
def grain (k:ℕ):ℝ:= (1:ℝ)/(k+1)
section click
-- known reserve independent p in payroll; well below any fixed positive power coupling inverse. Bound use `r` tending 0 by admitted k across Recruit. Good level clock min J pays flows, κ. Formal high uses this too.
open RemainderComparison Lyric
def spray (x : ℝ) : ℝ := Real.exp ( ( 1+ max 0 (Real.log (Real.log x)))^3)
lemma spray_late {G:Gauge}(q:ℕ): ∀ᶠ x:ℝ in atTop, (Delay.fineMonitor G L x)^q ≤ spray (betaF G x L):=by
    filter_upwards [((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop (q:ℝ)] with x hx
    let a:= Real.log (Real.log (betaF G x L)); have h0:a≥0:= (Nat.cast_nonneg q).trans hx
    unfold spray; rw [show max 0 a=a from max_eq_right h0]; change (Real.exp (a^2))^q≤_; rw [← Real.exp_nat_mul]; apply Real.exp_monotone; nlinarith only [h0,mul_le_mul_of_nonneg_right (show (q:ℝ)≤ a from hx) (sq_nonneg a),sq_nonneg a]
structure RoomR (μ x W:ℝ)(k s q:ℕ)(r:ℝ)(F:Postage)(A:Time.Forecast F)(o:ConnectedActivityE6.Target.Order G W)(U V':ℝ→ℝ):Prop where
  summer : Summer V k s (fun _=> 4) U V' W μ L o A x
  lightBand : Spire.fees L (P.below.supportExponent+1+1)+(U x)^k* V' x ≤ (betaF G x L) ^ r
  geom : Spire.fees L (P.below.supportExponent+1+1)+(U x)^k* V' x ≤ (Delay.fineMonitor G L x)^q
  growth : (Delay.fineMonitor G L x)^q ≤ spray (betaF G x L)
def Freq {P':Sheet G} {K:MapPrices} (M:Targets P' K)(u:ℕ→ℕ) := ∀ j i, StepStages j i→∀ L:Side,u j ≤ L.val→∀ W μ,0<W→0<μ→∀ o:ConnectedActivityE6.Target.Order G W,∀ (F:Postage)(A:Time.Forecast F), A.hard≤μ/32→∀ (s k:ℕ),1≤ s→∀ r:ℝ,0<r→ ∃ q U V',∀ᶠ t in atTop, RoomR (M j i) L μ t W k s q r F A o U V'
open Push.AbsoluteSums
variable {S:Sheet G}{Z:MapPrices} (M:Targets S Z)
lemma orbit (hf:∀ j i, StepStages j i→3/8+(M j i).rate<0)(he:∀ j i, StepStages j i→(S.profile i).supportExponent+1+1<(M j i).exp):∃ n:ℕ→ℕ,Freq M n:=by
  -- Build BEFORE L etc.
  have he j i : ∃ m :ℕ, ∀ (hp:StepStages j i) (L:Side),m≤ L.val→ ∀ W μ,0<W→0<μ→∀ o:ConnectedActivityE6.Target.Order G W,∀ (F:Postage)(A:Time.Forecast F), A.hard≤μ/32→∀ (s k:ℕ),1≤ s→∀ r:ℝ,0<r→ ∃ q U V',∀ᶠ t in atTop, RoomR (M j i) L μ t W k s q r F A o U V':= by
     by_cases h:StepStages j i; swap; · exact ⟨0,fun hf=> (h hf).elim⟩
     obtain ⟨n,hn⟩:=choices (M j i) (hf j i h) (he j i h); refine ⟨n,fun hi L hL W μ hW hμ o F A hA s k hs r hr=>?_⟩
     obtain ⟨U,V,hU,hV,hT⟩:= hn L hL W μ hW hμ k s hs o F A _ (Reserve.const _) hA
     let w:= Spire.fees L ((S.profile i).supportExponent+1+1)
     have hg:Rate G L 0 (fun x=> (U x)^k* V x):= by simpa using ((Rate.pow hU.rate k).mul hV.rate) -- simp
     obtain ⟨q,hq⟩:= (Reserve.const w).add ((hU.pow k).mul hV)
     refine ⟨q,U,V,?_⟩; filter_upwards [hT, ((Rate.const w).add hg) r hr, hq, spray_late (G:=G) L q] with x hv h hq hs; exact ⟨hv,(le_abs_self _).trans h,(le_abs_self _).trans hq,hs⟩
  choose h hh using he; exact ⟨fromMax h,fun j i he L ht=> hh j i he L ((le_fromMax h he).trans ht)⟩
variable {M D :Targets S Z}
structure Leg {j i:ℕ} {a : ℝ} (x:ℝ) (M:Targets S Z) (L:Side)(p:ℝ) (o:ConnectedActivityE6.Target.Order G a)(F:Postage)(A:Time.Forecast F) : Prop where
  income : let y:=betaF G x L; ∀ β,inBand y β→Payments.Rates (radiusB x) (Real.exp (-Pairing.kGoal F y β)) (A.pair.strong y β) (x^(-(1/3:ℝ))+Willow.haloSlack (radiusB x)) (Pairing.kGoal F y β)
  pretty : ∀ s:ℕ,s≤ i→∀ β,inBand (betaF G x L) β→Real.exp (-Pairing.kGoal F (betaF G x L) β)≤(betaF G x L)^(-(↑s:ℝ))*Blush.glyph x
variable {u u':ℕ→ℕ} {p:Return.Wages} {q:ℕ→ℝ} {D0:Rolls S} {Z':Expenses M} (R : PhysicalNext.Repeat.Register D0 Z' p q) (F : ℕ→ℕ→Postage) (A:Time.Scouts (F:=F))
def Celebrates (j i:ℕ)(x:ℝ): Prop:= Leg (j:=j) (i:=i) x M (D0.L j) (R.μ j i) (R.o j i) (F j i) (A j i)
variable {P0:Protection D0} (hpocket :PhysicalNext.Repeat.Pocket R A)
variable {j i:ℕ}
structure Frost (B:Delays P0):Prop where
   bears :∀ (j i:ℕ) (x:ℝ),StepStages j i → B.betaEntry j≤x → Celebrates R F A j i x
   license : ∀ j i:ℕ,StepStages j i→ ∀ k s:ℕ,k≤ i→s≤ i→1≤ s→∃ q U V',∀ x:ℝ,B.betaEntry j≤x→RoomR (M j i) (D0.L j) (R.μ j i) x (p j i) k s q (grain i) (F j i) (A j i) (R.o j i) U V'
include hpocket in
lemma option (hp:Freq M u)(hv:∀ i,u i ≤ (D0.L i).val) (B:Delays P0):∃ C:Delays P0,DelayLe B C∧∀ D:Delays P0,DelayLe C D → Frost R F A D:=by
   have hf (j i:ℕ)(hs:StepStages j i) (k s:ℕ): ∃ (q:ℕ) (P Q:ℝ→ℝ), ∀ᶠ x:ℝ in atTop,(1≤ s → RoomR (M j i) (D0.L j) (R.μ j i) x (p j i) k s q (grain i) (F j i) (A j i) (R.o j i) P Q):= by
      by_cases he:1≤ s; swap; · exact ⟨0,0,0,Eventually.of_forall fun x ht=> (he ht).elim⟩
      obtain ⟨q,P,Q,hP⟩:= hp j i hs _ (hv j) (p j i) (R.μ j i) (R.consumes j i hs).1 (R.consumes j i hs).2.1 _ (F j i) (A j i) (hpocket.price j i hs) s k he (grain i) (by unfold grain; positivity)
      exact ⟨q,P,Q, hP.mono fun x hx _=>hx⟩
   choose q f g0 hfg using hf
   let L j:= D0.L j;
   let pit x j i (h:StepStages j i) := Celebrates R F A j i x ∧ ∀ k s:ℕ,k≤ i→s≤ i→1≤ s→RoomR (M j i) (L j) (R.μ j i) x (p j i) k s (q j i h k s) (grain i) (F j i) (A j i) (R.o j i) (f j i h k s) (g0 j i h k s)
   have h j i (h:StepStages j i):∀ᶠ x:ℝ in atTop, pit x j i h:=by
      -- compare β calculus, no HP.S lost.
      filter_upwards [Willow.census (F j i) (A j i) (G.slopeConstant * Real.log ((L j).val:ℝ)) (Work.E04.shift_nonneg G _), (eventually_all_finset (Finset.Iic i)).mpr fun s hs=> divided (G:=G) (F j i) (L j) (-(↑s:ℝ)), (eventually_all_finset (Finset.Iic i)).mpr (fun k hk=> (eventually_all_finset (Finset.Iic i)).mpr (fun s hs=> hfg j i h k s))] with i' h₁ h₂ h₃; exact ⟨⟨h₁,fun s hs=> h₂ s (mem_Iic.mpr hs)⟩, fun k s hk hs=> h₃ k (mem_Iic.mpr hk) s (mem_Iic.mpr hs)⟩
   obtain ⟨V,-,hV,hH⟩:= collect_upper B.betaEntry (fun j x=>∀ i (hi:StepStages j i), pit x j i hi) (fun j=> by
     let T x i:= ∀ hi:StepStages j i,pit x j i hi
     have hz : ∀ᶠ x in atTop, ∀ i:ℕ,StepStages j i → T x i := eventually_transitions j _ _ (fun i (ht:StepStages j i)=> (h j i ht).mono fun x hx _=>hx)
     exact hz.mono fun x hx i ht=> hx i ht ht)
   exact ⟨{ B with betaEntry:=V},⟨hV,le_rfl,le_rfl,le_rfl⟩,fun U he=>⟨fun j i x ht hp=> (hH j x ((he.beta j).trans hp) i ht).1, fun j i ht k s hk hs hz=> ⟨_,_,_,fun x hx=>(hH j x ((he.beta j).trans hx) i ht).2 k s hk hs hz⟩ ⟩⟩
end click
end sheets
end YM.QuadraticLocal.Beaming
