import YM.Juniper.Gauze.Seams
import YM.Juniper.Bright.Boost
import YM.Juniper.LocalAtlas.Paid
/-!
 # Charge widths through epoch. Choose ANY n≤stage count. Real error v exponent leaf+2*leew
 prices uniformly stage ready; actual n,N levels. Some losses δ and soft meters. Don't claim E projection in arbitrary masks.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Gauze
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain LocalAtlas Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {L : Side} {c f:Side} {i j N m n:ℕ}
section pay
variable (G L) (X:RG.Stage) (n j k:ℕ) (a: Stars)
-- all signs auxiliary coaster prices. Use at parent. `coverTicket` explicit before geometry
local notation "V"=> betaF
local notation "B"=> (fun x=> Trio.base k (radiusB x))
local notation "Y"=> (fun x=> Trio.fence k (radiusB x))
local notation "S"=> Height.away X

def rampK (j n:ℕ):= leaf n+leew j
def climbed (j n:ℕ):= rampK j n+leew j
abbrev inkK (x:ℝ):= S * (((V G x L)^deep j+(V G x L)^deep j )+(V G x L)^deep j)
abbrev clouds (j n:ℕ)(x:ℝ):ℝ:= 3*(V G x L)^(rampK j n)
def courseK (x:ℝ):= ticket X.order (2*minds X.order (clouds G L j n x))+ 2*((Fintype.card (Site (Y x a)):ℝ)*inkK G L X j x)
def pie (x:ℝ) := (Trio.oroW (Time.probe X) (B x) (fun a:Stars=> courseK G L X n j k a x)) * Real.exp (Trio.stout X*coverTicket k)
def raiseK (x:ℝ) := inkK G L X j x+ S * pie G L X n j k x
-- don't claim estimates selecting Taylor order F paid in Final; Rates uniform via purchase.
section positive
variable {G L X n j k a}
lemma neutral {x:ℝ}(he:0 ≤ V G x L):0 ≤ inkK G L X j x:= by
   apply mul_nonneg (le_of_lt (turnFee_pos (Time.probe X))); positivity
lemma currency {x:ℝ}(he:0 ≤ V G x L):0≤courseK G L X n j k a x:= by
   have h:=neutral (X:=X) (j:=j) he; unfold courseK;apply add_nonneg _ (by positivity); unfold minds clouds Boulevard.ticket; positivity
lemma tints {x:ℝ}(he:0 ≤ V G x L):0≤ pie G L X n j k x:= by
    unfold pie Trio.oroW; refine mul_nonneg (Finset.sum_nonneg fun i _=>mul_nonneg (abs_nonneg _) (mul_nonneg ?_ (currency he))) (Real.exp_nonneg _); unfold Trio.tilt; positivity
lemma raise_nn {x:ℝ}(he:0 ≤ V G x L):0≤ raiseK G L X n j k x:= add_nonneg (neutral he) (mul_nonneg (turnFee_pos (Time.probe X)).le (tints he))
end positive

lemma dyeLe (h:n≤j): deep j ≤ rampK j n:= by
    unfold rampK LocalAtlas.leaf deep vow leew; have hp: 0≤ (j+1:ℝ)⁻¹:= by positivity
    push_cast; linarith only [hp, show (n:ℝ)≤j from Nat.cast_le.mpr h, Nat.cast_nonneg (α:=ℝ) n]
lemma feathers (h:n≤j): Rate G L (rampK j n) (inkK G L X j) ∧ Rate G L (rampK j n) (pie G L X n j k) ∧ Rate G L (rampK j n) (raiseK G L X n j k):= by
    have ht: Rate G L (rampK j n) (inkK G L X j):= let p:=Rate.power (G:=G) (L:=L) (a:=deep j); (((p.add p).add p).mul_left _|>.weaken (dyeLe n j h))
    have he a': Rate G L (rampK j n) (courseK G L X n j k a'):= by
       have h' : Rate G L (rampK j n) (clouds G L j n):= Rate.power.mul_left _
       apply Rate.add ((((((h'.mul_left _).mul_left _).mul_left _).mul_left _).mul_right _)); simpa only [zero_add] using! (((feeStars G L k a').mul ht).mul_left 2)
    have hq:Rate G L (rampK j n) (pie G L X n j k):= by
       apply Rate.mul_right (a:=rampK j n) (w:=fun x=> Trio.oroW (Time.probe X) (B x) (fun i=> courseK G L X n j k i x)); refine sparks G L (f:=fun i x=>|Slide.ray i| * _) ?_; intro i; have hv: Rate G L 0 (fun x=>Trio.tilt (Time.probe X) (B x)):= ((Bolt.still ((2:ℝ)^X.order)).times (((Bolt.still 1).joins (Trio.rows G L k|>.2.2.1)).nod (X.power*X.order))).uses
       simpa only [zero_add] using! (((hv.mul (he i)).mul_left |Slide.ray i|))
    exact ⟨ht,hq,ht.add (hq.mul_left _)⟩
lemma hue (P : BudgetPoint) (H: Time.Same X P) (x:ℝ) : (Trio.oroW P (B x) (fun a:Stars=> courseK G L X n j k a x)) *Real.exp (preExponent P *coverTicket k) = pie G L X n j k x:= by simp only [Trio.oroW, pie, preExponent, Trio.tilt,H.1,H.2.1,H.2.2,Trio.stout, Time.probe]

def betaK (x:ℝ) := (betaF G x L) ^ climbed j n
lemma sail (h:n≤j) : ∀ᶠ x in atTop, raiseK G L X n j k x ≤ betaK G L n j x ∧ pie G L X n j k x ≤ betaK G L n j x := by
    obtain ⟨h₁,h₂,h₃⟩:= feathers G L X n j k h; have he : rampK j n<climbed j n:=lt_add_of_pos_right _ (by unfold leew; positivity); filter_upwards [h₂ (climbed j n) he,h₃ (climbed j n) he] with x h hp using ⟨(le_abs_self _).trans hp, (le_abs_self _).trans h⟩
end pay
end YM.Juniper.Gauze
