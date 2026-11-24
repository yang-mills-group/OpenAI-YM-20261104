import YM.RGComparison01.Kraal

/-!
# Further bill mathematics

 All geometric budgets on weighted memories. Choose post costs and periods
 for the reflection interpolation and restore sections. Every fee still to
 be paid on the same witness. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling
open Further.PhysicalPeriodLimitF933
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' T : ℝ} {q q' n k b p w: ℕ} {v d W u : ℝ→ℝ}
namespace Vision
-- Geometry. Pay ∀ n common stage transition tests. Short model input can use `g*B`
abbrev Hall (m g r B : ℕ) := Cabinet.studio (Deck.Mint.width m B (B+g*B)) r B
abbrev escrow (m g r : ℕ) := Hall m g r 1
lemma shapes (m g r B:ℕ) (ht:1 ≤ B) : Hall m g r B ≤ Meadow.studio (escrow m g r) B:= by
  let V:= Deck.Mint.width m 1 (1+g*1); let W:= Deck.Mint.width m B (B+g*B)
  have hp : W ≤ V * B:= by unfold V W Deck.Mint.width; nlinarith only [ht]
  have hv : Hall m g r B ≤ escrow m g r*B:= by
    unfold Hall escrow Hall Cabinet.studio Cabinet.garage
    change _≤ ((r*r*(4*V+2)+2*V)+2*1)*B
    change (r*r*(4*W+2)+2*W)+2*B ≤ _
    nlinarith only [Nat.mul_le_mul_left (r*r) hp,ht,hp,Nat.mul_le_mul_left (r*r) ht]
  exact hv.trans (by unfold Meadow.studio Meadow.roomSize Deck.Mint.width; omega)

-- loose due. early exponent +1+1
open Starlight
variable (G : Gauge) (L : Side) (p q r : ℕ)
local notation "A" => Vision.escrow p q r
-- copy discipline for all stages. fees expressed in STAGE port args so Defeq bindings
variable (U : RG.Stage)
abbrev shelf (x:ℝ) := Height.away U * (betaF G x L^(-(7/16):ℝ)+ betaF G x L ^ (-(7/16):ℝ)) -- Factor.volume uses (Z.wanting=-7/16)
abbrev heater (x:ℝ) := (ballCost (Vision.Hall p q r (radiusB x)):ℝ)*shelf G L U x
abbrev Hat (f : ℝ→ℝ) (x : ℝ) := |f x| * (2*gStep (Pressure.betaF G x L))
-- assent Y = p model intentionally paid on Hat
abbrev guessT (f : ℝ→ℝ) (x:ℝ) := Starlight.hotB (Trio.fence (Vision.escrow p q r) (radiusB x)) (Vision.Hall p q r (radiusB x))
    (Vision.Hat G L f x) (Vision.shelf G L U x) (fun _=> Vision.heater G L p q r U x+ Vision.Hat G L f x)
lemma shiftH : Bolt G L (fun x=> (Vision.Hall p q r (radiusB x):ℝ)) := by
  have he:= Bolt.size (G:=G) (L:=L)
  let V x:= Deck.Mint.width p (radiusB x) (radiusB x+q*radiusB x)
  have ht: Bolt G L (fun x=> (V x:ℝ)):= by
    unfold V Deck.Mint.width; push_cast; exact (((Bolt.still _).times he).joins (((Bolt.still _).times he).joins (Bolt.still _))).joins (he.joins ((Bolt.still _).times he))
  have hv : Bolt G L (fun x=> (Cabinet.garage (V x) r:ℝ)):= by
    unfold Cabinet.garage; push_cast
    exact ((Bolt.still _).times (((Bolt.still _|>.times ht)).joins (Bolt.still 2))).joins ((Bolt.still 2).times ht)
  change Bolt G L (fun x=> ((Cabinet.garage (V x) r + 2*radiusB x:ℕ):ℝ)); push_cast; exact hv.joins ((Bolt.still 2).times he)
lemma crust : Rate G L (-(7/16)) (Vision.heater G L p q r U) := by
  simpa only [zero_add] using! ((Trio.balls G L (f:=fun x=> Vision.Hall p q r (radiusB x)) (Vision.shiftH G L p q r)).mul (((Rate.power (G:=G) (L:=L)).add (Rate.power)).mul_left _))
lemma guessing (f : ℝ→ℝ) (h : Geo G L f) : Rate G L (-(7/16)) (Vision.guessT G L p q r U f) := by
  let H:= heater G L p q r U; have hp:= Vision.crust G L p q r U
  let X:= Hat G L f
  have hx : Rate G L (-(7/16)) X := (h.mean.rate.mul (Sienna.glim G L)).weaken (by norm_num)
  let Y:= hp.add hx
  let Y' (i:Stars) x := |Slide.ray i| * ((Fintype.card (Site (Trio.fence A (radiusB x) i)):ℝ)*(H x+X x+(H x+X x)))
  have hs i : Rate G L (-(7/16)) (Y' i):= by simpa only [zero_add] using! (((Trio.feeStars G L A i).mul (Y.add Y)).mul_left |Slide.ray i|)
  exact Rate.add (Y.add Y) (Trio.sparks G L hs)
lemma pundit (f : ℝ→ℝ) (h:Geo G L f): ∀ᶠ t in atTop, ∀ B:BudgetPoint,
    B.B=radiusB t → B.supportExponent= U.supportExponent → Marlin.tithe (2*Trio.base A (radiusB t)) (Vision.guessT G L p q r U f t) B (Trio.coverTicket A) ≤ Pressure.betaF G t L^ (-(1/8):ℝ) := by
  have hp:= Vision.guessing G L p q r U f h
  let b x:= 2*Trio.base A (radiusB x)
  have hv:= (((Trio.balls G L (f:=b) (Trio.rows G L A|>.2.2.2)).mul hp).mul_right (Real.exp ((U.supportExponent+1+1)*Trio.coverTicket A))) (-(1/8):ℝ) (by norm_num)
  filter_upwards [hv] with t ht B hB hE
  unfold Marlin.tithe; rw [hE]; exact (le_abs_self _).trans ht
end Vision
end YM.RGComparison01
