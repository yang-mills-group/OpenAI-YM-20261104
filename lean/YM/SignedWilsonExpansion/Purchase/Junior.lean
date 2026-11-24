import YM.SignedWilsonExpansion.Purchase.Imburse
import YM.Integration.WilsonPositionProgramSubmittedGeometry
/-! # All-rank berth cost on issued horizon. Adapter for Oven: one Euclidean pillar composite via Alpine canon.
 All dates in the measured Wilson clocks, UIView.Fore support. No clock substitution with the Showcase clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 670000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense Ticket Cosmos Cosmos.Polestar Source MarqueQ Method Stair FVA2 FVA2.Scale
open StationA Reef
open Precision
open RegulatorIR RegulatorIR.Motion RegulatorIR.Profiles RegulatorIR.Cluster
open scoped Topology Classical BigOperators
variable {G:Gauge}{S:Schedule}{M:Levels G}{e n h d k u K l c:ℕ}{T:Initialize G}{ι J:Type} -- Run namespace ambiguous
local notation "Λ"=> Fin (n+1)
def combR (n:ℕ)(f: Fin (n+1)→J): Composite J:=match n with
   | 0=> .atom (f 0)
   | n+1=> .pair (.atom (f 0)) (combR n (Fin.tail f))
abbrev wholeP (n:ℕ):= combR n id
lemma census (f:Λ→J)(y:J→ℕ): (combR n f).accounts y=∑ i:Λ,y ( f i ):=by
   induction n with| zero=> simp only [combR,Composite.accounts,Fintype.sum_unique]; rfl | succ n ih=> rw [combR,Composite.accounts,Composite.accounts, Fin.sum_univ_succ (n:=n+1),ih]; rfl
lemma cereal_rank (v:Λ→Pill G)(k:ℕ)(p:∀ i,(v i).rank≤k): homeRank v (wholeP n)≤(n+1)*k:=by
   rw [homeRank,wholeP,census]; apply le_trans ( Finset.sum_le_sum (g:=fun _:Λ=>k) (fun i _=>p i) ) (?_); simp
variable {p₀:Period} (W:p₀.Tree)(f:J→Pill G)(x:J→ Cover)(t:Fin (n+1)→J)
lemma welcomeP : Reef.welcome f x (combR n t)= embark (fun i=>(f (t i)).letter) (x ∘ t):=by
   unfold embark; induction n with | zero=> rfl| succ n ih=> rw [combR, Reef.welcome,ih,MassP]; rfl
lemma rollerP : Reef.main f x p₀ W (combR n t)=∏ i, StationA.propose W ( wrap p₀.side ( x ( t i ))) (f ( t i )):=by
   induction n with | zero=> simp only [ combR, Reef.main, Reef.foldR,Fin.prod_univ_succ, Finset.univ_eq_empty,Finset.prod_empty, mul_one ]| succ n ih=> rw [combR, show Reef.main f x p₀ W (.pair (.atom ( t 0 )) (combR n (Fin.tail t)))= _ * _ from (rfl : _ = StationA.propose W _ (f (t 0)) * Reef.main f x p₀ W (combR n (Fin.tail t))), Fin.prod_univ_succ, ih]; rfl
open Minty
-- data, *measured* ladder Ξ. Meter arbitrary after C selection. Σ budget after orientation homology.Loan rails: power of 3 exactly step of world.
def normalizedInsertionSeries (v:Λ→Pill G)(w:Λ→ Cover)(g:Mesh)(T:Initialize G): PowerSeries ℂ:= Bare.normalized (T.tree g.p) G (Reef.main v w g.p (T.tree g.p) (wholeP n))
def initialClock (A:Levels G)(Ñ: ChartRatio G)(l c:ℕ)(v:Λ→Pill G)(w:Λ→ Cover): PowerSeries ℂ := insertQ ( rear A Ñ c l c ( FadeRaw A Ñ c (homeRank v (wholeP n)) l c (Reef.welcome v w ( wholeP n ))))
abbrev widthY (A:Levels G)(l c:ι→ℕ)(i:ι):ℝ:= (orbitP A.S (l i) (c i)).side.val
def amountV (A:Levels G)(l c:ι→ℕ)(t:ℝ)(z:ι→ℕ)(i:ι):ℝ:= 1+(2+log (A.clock.hatBeta (c i)))+|log (widthY A l c i)|+(max 0 t+1)*(3:ℝ)^(z i)
-- note: x revenue.Round 
open Integration.WilsonPositionProgramSubmittedGeometry (center)
def MeterD (A:Levels G)(ρ:ι→ℝ)(h:∀ i,0<ρ i)(l c:ι→ℕ)(t:ℝ)(w:ι→ Λ→ Cover)(z:ι→ℕ) :=
   ∀ i,let F:= roof A (l i) (c i) (ρ i) (h i); 1+ Reef.Ear.span (center F (lumber F)) ( w i ) (wholeP n) ≤ amountV A l c t z i
structure Campfire (I:Type)(G:Gauge)(e:ℕ)(A:Levels G)(Ñ:ChartRatio G)(T:Initialize G)(start:ℕ):Prop where
   exits (n:ℕ)(v:Fin (n+1)→Pill G)(l c:I→ℕ)(p:I→ℝ)(h:∀ i,0<p i)(s:∀ x,start≤l x) -- fix
       (hc:∀ i,l i≤ c i)(w:I→ Fin (n+1)→ Cover)(x:I→ℕ)(t:ℝ)(y:MeterD A p h l c t w x) (q:ℕ)(hp:q≤e):
       ∃ C:ℝ,∃ k:ℕ,0≤C∧∀ i,
       ‖PowerSeries.coeff q ( normalizedInsertionSeries v ( w i ) (roof A (l i) (c i) (p i) (h i)) T ) - PowerSeries.coeff q ( initialClock A Ñ (l i) ( c i ) v (w i))‖ ≤ C * amountV A l c t x i^k * (widthY A l c i)^(-(1/4:ℝ)) -- define

-- padding `k` comparison Exact through ℓ. Not postposing rockets till cutoff.Flat in Epoch only.
lemma extendR (P:Era G ℝ)(q:Auth k P)(p:l≤c){Ñ:ChartRatio G}(r:G.Simple)(y:LocalRatio Ñ)(v:c≤u)(a:k≤h): cruises M Ñ u k c l P=cruises M Ñ u h c l P:=by
   induction p using Nat.decreasingInduction with
   | self=> rw [cruises_top,cruises_top]
   | of_succ i t ih=> rw[cruises_sub _ _ _ _ P t, cruises_sub _ _ _ _ P t,←ih]; exact verseExpand _ (t.trans_le v) r y (cruising M r y t v q) a
lemma cosmosP (p₀:XSpace.Mesh) (x:Λ→ Cover)(Z: Λ→ Pill G) : normalizedInsertionSeries Z x p₀ T= LampNow (T.tree p₀.p) (fun i=> StationA.propose (T.tree p₀.p) (wrap p₀.p.side (x i)) ( Z i )):=by unfold normalizedInsertionSeries wholeP; rw [rollerP]; rfl
lemma earsP (x:Λ→ Cover)(Z:Λ→ Pill G)(p:∀ i,(Z i).rank≤k){Ñ:ChartRatio G}(r:G.Simple)(y:LocalRatio Ñ)(v:l≤c): initialClock M Ñ l c Z x=PhaseAge x M Ñ c l k (fun i=>(Z i).letter):=by unfold initialClock PhaseAge FadeRaw; rw [extendR _ ( Reef.kinetic .. ) v r y le_rfl (cereal_rank _ k p), wholeP, welcomeP]; rfl
lemma spanP (t:J→ Cover)(w:Fin (n+1)→J)(x:Room): Reef.Ear.span x t (combR n w)= ∑ i:Λ,dist x (slide 1 (t ( w i ))):=by
    induction n with| zero=> simp only [combR, Reef.Ear.span,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero] | succ n ih=> rw [combR, Reef.Ear.span,Fin.sum_univ_succ, ih]; rfl -- notation mism?
-- bureaucratic.Spacing at clamped row. Economy
lemma widthCost (A:Levels G)(l c:ι→ℕ)(T:ℕ)(i:ι): (1:ℝ)≤ widthY A l c i:= by exact_mod_cast (orbitP A.S _ _).side.pos
abbrev feels (M:Levels G)(l c:ι→ℕ)(B:ι→ℝ)(L:Filter ι):= Consume B L 1 (log ∘ widthY M l c) -- log upper enough
variable {l c:ι→ℕ}{B ρ:ι→ℝ}{L:Filter ι}
lemma widthRatio {i:ι}(u: l i≤ c i): log (widthY M l c i) = Real.log 16 + M.S.scale (c i) - M.S.scale (l i):=by
     let P:= parcel M.S (l i) (c i); have hx: 0<(P:ℝ):= Nat.cast_pos.mpr ( gain_pos .. ); rw [widthY]; change log ((16*P:ℕ):ℝ)= _; push_cast; rw [Real.log_mul (by norm_num) hx.ne',add_sub_assoc, Schedules.σStub M, ← parcel_size M.S u,mul_div_cancel_right₀ _ (M.S.a_pos _).ne']
variable (q:Rise B L)
include q
lemma feePoly {x:ι→ℝ}(p:Wage L ( Spread B ) 1 x){X:ℝ}(hp:0<X): Consume B L X x:=by
    have hx:= polyLeM q p; exact hx.trans (( Minty.spendMark (E:=0) (U:=1) q (by unfold Consume; rw [payD_zero]) hp 1).isBigO.congr_left fun i=> by simp)
lemma width_charge (p: l≤ᶠ[L] c)(ht:hemisphere M L B l c): feels M l c B L:=by
     have hp:= Wage.plus ((y_rise q).eventually_ge_atTop 1) ( Wage.unitC ( Real.log 16 )) ht; exact feePoly q (hp.fix ( p.mono fun i hi=>by rw [Function.comp_apply, widthRatio hi]; ring ) (.refl ..)) zero_lt_one
end YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking
