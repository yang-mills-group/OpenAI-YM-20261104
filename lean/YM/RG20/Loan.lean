import YM.UVExtension.Orchard.Racks
/-! # True Cart metric at the common full UV reconstruction. Expose REAL costing, using
 all the E/K support and displacement norms, not on values after applying a patch. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG20.Loan
open Function Filter Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory UVExtension Spire Dales Guild Push Oriel Oriel.Charted Camp Camp.Cart Fitted Orchard
set_option quotPrecheck false
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{R : Factor A}(S: Spire.Uses R hG)
    (v : Keys S) {N p i:ℕ}
local notation "T"=> A.B.a
local notation "D"=> (S.fits N p)
local notation "E"=> (S.cart N p)
local notation "α"=> (A.B.kin.alpha N)
local notation "κ"=> (S.grove.coins)
local notation "π"=> (S.grove.pledge)
local notation "s"=> (S.grove.peak)
local notation "rp" i=> (D).W (i)

abbrev vertex (N p i:ℕ):= Fitted.Home (S.fits N p) i
abbrev ζnorm (N p i:ℕ) := place T i p ((S.fits N p).W i) -- REAL in Hut; any Grip displacement can price all arrays simultaneously
abbrev sitecharge (N p i:ℕ) (x:vertex S N p i):= ‖ζnorm S N p i x‖
abbrev etaPack (N p i:ℕ)(x:vertex S N p i):= Tabernacle.floor ((A.B.a).budget i) x.val
abbrev levelPlot (N p:ℕ) := Fitted.sonnet (S.fits N p) (S.cart N p) (S.grove.coins) ((v N p).val:ℂ)
abbrev money (N p : ℕ) := (S.fits N p).Third (S.cart N p) S.grove.coins (v N p).val
abbrev actual (N p :ℕ) := (S.fits N p).Rest (S.cart N p) S.grove.coins (v N p).val
abbrev scalarBook (N p :ℕ):= (S.fits N p).Sail (S.cart N p) S.grove.coins (v N p).val -- leave at true, separately
abbrev H := Orchard.Path S v

local notation "ß"=> (money S v N p)
local notation "ℒ"=> (actual S v N p)
local notation "℃"=> (scalarBook S v N p)
local notation "s!"=> (levelPlot S v N p)
local notation "τ"=> S.token N p
local notation "Y" i=> ((Loan.H S v).rep N p (i))
local notation "Ψ" i=> sitecharge S N p (i)
local notation "δ"=> A.B.a.clock
local notation "∆" i=> ζnorm S N p (i)
local notation "δE"=> A.B.a.clock.allowance
local notation "δK"=> A.B.a.clock.forcedAllowance

-- price uses exactly the chosen local alphabet of this cutoff, fields and queries
lemma price_charge (x:vertex S N p i) (a:ℝ) : sitecharge S N p i x ≤ a ↔ (etaPack S N p i x).Valid ((T).budget i) (a * (δE) i) (a * (δK) i):=
   Tabernacle.tickP _ _ _ (fundedP .. |>.1) (fundedP ..|>.2) ((D).W i|>.income _ x|>.1)
lemma lane (N p i:ℕ) : RG.Rep.mk ((A.B.kin.path N i)) ((A.B.a.params i).clip) (etaPack S N p i (actual S v N p i)) (A.B.a.budget i) ((money S v N p i)) (scalarBook S v N p i)=(Loan.H S v).rep N p i:= rfl

local notation "ζ"=> Oriel.rim
include v
lemma head_of : Fitted.Shot D ℒ ß (℃):= ((D).acts E (S.token N p) κ (v N p).2).1
lemma levelBet (hi:i≤ N): lock R (levelPlot S v N p) i hi = ß i:=by
   unfold money Third faceV; rw [dif_pos hi]
lemma sung (hi:i≤ N): Camp.Cart.play T N ((D).Hut) E s! i hi=(∆ i) (ℒ i):= Fitted.really D E τ κ (v N p|>.property) i hi |>.2
lemma pricelist (hi:i≤ N): sitecharge S N p i (ℒ i)≤ Camp.soft:= by rw [sitecharge, ← sung S v hi]; exact ((D).riversV E κ i hi).2 _ (v N p).property
lemma softly (hi:i≤ N): Reality T i p ((D).W i) (ℒ i) (ß i):= (head_of S v).alive _ hi
lemma credit (x:vertex S N p i)(hi:i≤N)(hp:sitecharge S N p i x < Oriel.rim): Reality T i p ((D).W i) x (ß i):=
   ⟨(softly S v hi).1,hp.le.trans (by norm_num [Oriel.rim])⟩
abbrev splitPoint (N p i:ℕ)(hi:i≤N)(x:vertex S N p i) := ((Camp.Cart.node N (levelPlot S v N p) i hi).re,x) -- real slice signed offset axis
abbrev joy (N p i:ℕ)(hi:i≤N)(x:vertex S N p i):= river T i p ((S.fits N p).W i) (splitPoint S v N p i hi x)
lemma emerges (x:vertex S N p i)(hi:i≤N)(hh:sitecharge S N p i x < Oriel.rim): Loan.joy S v N p i hi x∈ Grip:=by
   apply mem_ball_zero_iff.mpr; rw [Loan.joy,Dales.eddies]; apply max_lt ?_ hh
   let p':= (E).pivot T N ((D).Hut) s! i hi; have h := (E).seats T N ((D).Hut) ((D).glint E κ _ (v N p).2) i hi |>.2
   apply (Complex.abs_re_le_norm _).trans_lt; apply max_lt_iff.mp (show max ‖p'.1‖ ‖p'.2‖< Oriel.rim from mem_ball_zero_iff.mp h) |>.1
lemma currencies (x y:vertex S N p i)(hi:i≤N) : ‖Loan.joy S v N p i hi x-Loan.joy S v N p i hi y‖=sitecharge S N p i (x-y):=by
   unfold joy; rw [← map_sub,Dales.eddies]; unfold splitPoint; change max |(node ..).re-(node ..).re| _=_ -- elaboration may fail
   rw [sub_self,abs_zero]; exact max_eq_right (norm_nonneg _)

abbrev roller (N p i:ℕ)(hi:i<N)(x:vertex S N p (i+1)) : vertex S N p i:= Dales.Tour.choiceV R hG (S.grove.pledge) ((S.fits N p).charts i hi) ((S.fits N p).W (i+1)) ((S.fits N p).shirts i hi) x (money S v N p (i+1))
abbrev coins (N p i:ℕ)(hi:i<N)(x:vertex S N p (i+1)):= Dales.Tour.claim R ((S.fits N p).charts i hi) ((S.fits N p).W (i+1)) x (money S v N p (i+1))

lemma opening (hi:i<N) (x:vertex S N p (i+1)) (hp:sitecharge S N p (i+1) x< Oriel.rim) : (E).car i hi (Loan.joy S v N p (i+1) hi x)= ζnorm S N p i (roller S v N p i hi x)∧(E).gain i hi (Loan.joy S v N p (i+1) hi x)=↑(coins S v N p i hi x):=by
    have h:= emerges S v x hi hp; let t:= splitPoint S v N p (i+1) hi x; rw [Loan.joy,Dales.Order.ray ((τ).phase i hi) t h, Dales.Order.ray ((τ).pigment i hi) t h]; change ζnorm S N p i (((D).charts i hi).choiceV R hG π _ ((D).shirts i hi) x (lock R s! _ hi))=_ ∧ (↑(Dales.Tour.claim R ((D).charts i hi) _ x (lock R s! _ hi)):ℂ)=_
    rw [levelBet S v hi]; exact ⟨rfl,rfl⟩
lemma shore (hi:i<N)(x y:vertex S N p (i+1))(hx:sitecharge S N p (i+1) x < Oriel.rim)(hy:sitecharge S N p (i+1) y < Oriel.rim) :
    sitecharge S N p i (roller S v N p i hi x) ≤ Camp.soft ∧
    sitecharge S N p i (roller S v N p i hi x-roller S v N p i hi y) ≤ Camp.soft * sitecharge S N p (i+1) (x-y)∧
    |coins S v N p i hi x-coins S v N p i hi y|≤ Yard.rake ((δ).hatBeta (i+1))*sitecharge S N p (i+1) (x-y):=by
    let x':= Loan.joy S v N p _ hi x; let y':= Loan.joy S v N p _ hi y; have h:= (E).cargo i hi; have hp:= (E).coin i hi; have hX:=emerges S v x hi hx; have hY:=emerges S v y hi hy; obtain ⟨ha,hA⟩:=opening S v hi x hx; obtain ⟨hb,hB⟩:= opening S v hi y hy;
    have hq:=h.amounts x' hX y' hY; have hh:= hp.amounts x' hX y' hY; unfold x' y' at hq hh; rw [ha,hb,currencies,← map_sub] at hq; rw [hA,hB,currencies,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh; exact ⟨(congr_arg Norm.norm ha.symm).trans_le (h.rises _ hX),hq,hh⟩
lemma summitBill (hi:i<N): ℒ i = roller S v N p i hi (ℒ (i+1)) ∧
    ß i = ß (i+1) + A.B.kin.alpha N i + coins S v N p i hi (ℒ (i+1)):=by
    have h:= softly (p:=p) S v (show i+1≤N from hi); obtain ⟨hb,ha,H'⟩:= (D).doors (head_of S v) i hi
    unfold roller coins; rw [Tour.claim,Tour.choiceV,dif_pos h,dif_pos h]; exact ⟨ha,hb⟩
end YM.RG20.Loan
