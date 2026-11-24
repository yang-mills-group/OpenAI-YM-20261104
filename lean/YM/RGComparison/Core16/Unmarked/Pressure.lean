import YM.RGComparison.Core16.Unmarked.Transit
import YM.UVExtension.Spire.Orbs
/-!
# Uniform unmarked step, in the pinned UV Valve

Work in coupling variables `b=β -- actual beta = g^-2`; in spatial window times producer
estimates can be implemented with arbitrary β satisfying `UVExtension.Lamppost.InsideB` (innermost interval
to pad the small complex disk analoguous to Health at the center -- stronger than band; physical
history stays UVExtension.Lamppost.InsideB at all valid steps). `credit` seminorm is EXACT suppower, mask & path
reserve semantics on the actual Fitted (See tickP proof). Full extensive scalar chosen in `run`,
not estimated by omission in equality. Can compare at different vac scalars without computing them
first. Elementary fallback `Credit(W-V)` not estimated by subtracting evaluations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Unmarked
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open UVExtension UVExtension.Guild UVExtension.Concert UVExtension.Spire UVExtension.Dales UVExtension.Camp.Cart
open UVExtension.Oriel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A}
   {hG:G.Simple}
variable (S:Uses R hG) {N m n:ℕ}
set_option quotPrecheck false
local notation "a!"=> A.B.a
local notation "H!"=> S.fits N n
local notation "W0"=> (S.fits N n).W

/-- Compatible labels/permutations, in the actual joint history. -/
abbrev Render (S:Uses R hG) (m N p:ℕ):=(S.fits N p).Home m

/-- The real-chart budget used here. Includes exponent reserves in `Levels.budget m` only, not an extra +2 reserve.
    Off mask values lie in a seminorm kernel but must be BILLed with ordinary
    obligations (`copied`). -/
def credit {m N n:ℕ} (x:Render S m N n):= ‖place a! m n ((S.fits N n).W m) x‖

variable {S}
def enact (x:Render S m N n) (β s:ℝ):=mount R N m n x.val β s
abbrev Favored {m N n:ℕ} (x:Render S m N n):= credit S x< UVExtension.Oriel.rim
abbrev hat (_S:Uses R hG)(m:ℕ) : ℝ:= (A.B.a.clock.hatBeta m)
lemma costs (x:Render S m N n)(a:ℝ): credit S x ≤ a ↔ (UVExtension.Tabernacle.floor (A.B.a.budget m) x.val).Valid (A.B.a.budget m) (a*(a!).clock.allowance m) (a*(a!).clock.forcedAllowance m):= by
    have hp:= Dales.fundedP m a!
    exact UVExtension.Tabernacle.tickP ((a!).budget m) _ _ hp.1 hp.2 (((H!).W m).income _ x).1
lemma valid {x:Render S m N n} (hx:Favored x): (enact x 0 0).activities.Valid ((a!).budget m) ((a!).clock.allowance m) ((a!).clock.forcedAllowance m):= (tapT m n a! (W0 m) x).1 (hx.le.trans (by norm_num [UVExtension.Oriel.rim]))

variable (hm: m<N) (x:Render S (m+1) N n)
def head (_S:Uses R hG)(N m:ℕ):= A.B.kin.alpha N m

def surge (β:ℝ): ℝ := head S N m + Dales.Tour.claim R ((H!).charts m hm) (W0 (m+1)) x β

def course (β:ℝ):Render S m N n:= Tour.choiceV R hG S.grove.pledge ((H!).charts m hm) _ ((H!).shirts m hm) x β

def run (β s:ℝ):= enact (course hm x β) (β+surge hm x β) (flatRate a! m n (enact x β s))

lemma operated (s:ℝ){β:ℝ}(he:Reality a! (m+1) n (W0 (m+1)) x β): run hm x β s=((H!).charts m hm).speck R _ he s:= by
    unfold run surge course enact
    rw [Tour.around (H:=(H!).charts m hm),Tour.choiceV, Tour.claim, dif_pos (show _ from he), dif_pos (show _ from he),←add_assoc]
    rfl
local notation "Y"=> hat (S) (m+1)
local notation "U"=> (a!).params m
lemma accounted (s:ℝ){β:ℝ}(he:Reality a! (m+1) n (W0 (m+1)) x β): let Q:= run hm x β s
    let B:= enact x β s
    Q.eval=((a!).clock.op m n).push β B.eval ∧ Q.Lawful (U).width (U).paths ((a!).clock.loopCap m) ((a!).clock.allowance m) ((a!).clock.forcedAllowance m) ∧ Q.activities.KBound ((a!).budget m) (Return.forcing A.B m) := by
    dsimp only []; rw [operated hm x s he]; let H:= ((H!).charts m hm)
    exact transits R hm H.atTopH H.W H.k (P₁:=enact x β s) rfl (H.oracle R (W0 (m+1)) he s) S.grove.pledge H.hr hG
lemma charge_kin {β:ℝ}(he:Reality a! (m+1) n (W0 (m+1)) x β): ((a!).clock.threshold m)^2 * |surge hm x β - head S N m| ≤ Time.credit G (U) * (a!).clock.allowance m:= by
    rw [surge, add_sub_cancel_left, Tour.claim, dif_pos he]; let H:= ((H!).charts m hm); let J:=H.oracle R _ he 0
    have hz : (mount R N (m+1) n x.val β 0).p= _:=(rfl : (mount R N (m+1) n x.val β 0).p=(a!).budget (m+1))
    have hv:= ready R hm H.atTopH H.W H.k J.atH (J.links R H.atTopH) rfl J.related J.price J.aisle hz S.grove.pledge H.hr
    exact Averaging.delta_bound hG hv.projects

open UVExtension.Tabernacle
-- beta of any next unmarked REAL step is UVExtension.Lamppost.InsideB to use this complex-character-independent
-- Lipschitz receipt; not asserting general Wants.Build buys means of thresholds outside admitted
-- band. Input x may be any linear combination in the chart, Favored, and no positivity assumptions.
variable {β:ℝ}(hk:UVExtension.Lamppost.InsideB (hat S (m+1)) β)
include hk in
lemma favor_box {x: Render S (m+1) N n}(he:Favored x): Reality a! (m+1) n (W0 (m+1)) x β:= by
    obtain ⟨hl,hu⟩:= hk
    have h0 : 1 < hat S (m+1):= (a!).fits.delayed (m+1)
    refine ⟨⟨?_,?_⟩,he.le.trans (by norm_num [rim])⟩
    · change hat S (m+1)/2 ≤ _; linarith only [hl,h0]
    change β ≤ 2*hat S (m+1); linarith only [hu,h0]
private abbrev post (x:Render S (m+1) N n):Flows a! (m+1) n (W0 (m+1)) := (0,x)
private lemma inside {x:Render S (m+1) N n}(he:Favored x): river a! (m+1) n (W0 (m+1)) (post x) ∈ Charted.Grip:= by
    rw [Charted.Grip, mem_ball_zero_iff, eddies]; exact max_lt (by norm_num [post, UVExtension.Oriel.rim]) he
private lemma rule : art Y β (post x).1=β:= by unfold post art; dsimp only; ring
variable (he:Favored x)
include hk he
lemma earns : credit S (course hm x β) ≤ UVExtension.Camp.soft ∧ |surge hm x β - head S N m| ≤ UVExtension.Yard.rake Y:= by
    let Q:= ((H!).charts m hm)
    obtain ⟨⟨F,hF⟩,⟨B,hB⟩⟩:= Dales.shelves R hG S.grove.pledge Q (W0 (m+1)) S.grove.enabled hk ((H!).shirts m hm)
    have ht:= inside he; let y:= river a! (m+1) n (W0 (m+1)) (post x)
    have hh: B y=place a! m n (W0 m) (course hm x β):= (hB.ray (post x) ht).trans <| by unfold marble; rw [rule]; rfl
    have hz: F y= ((surge hm x β-head S N m:ℝ):ℂ):= (hF.ray (post x) ht).trans <| by unfold Dales.flowing surge; rw [rule,add_sub_cancel_left]
    refine ⟨?_,?_⟩
    · unfold credit; rw [← hh]; exact hB.bounds.2.1 y ht
    have hp:= hF.bounds.2.1 y ht; rw [hz, Complex.norm_real] at hp; exact hp

lemma repeated_gain (x':Render S (m+1) N n)(hh: Favored x'): credit S (course hm x β-course hm x' β) ≤ UVExtension.Camp.soft*credit S (x-x') ∧
    |surge hm x β - surge hm x' β| ≤ UVExtension.Yard.rake Y*credit S (x-x'):= by
    let Q:= (H!).charts m hm
    obtain ⟨⟨F,hF⟩,⟨B,hB⟩⟩:= Dales.shelves R hG S.grove.pledge Q (W0 (m+1)) S.grove.enabled hk ((H!).shirts m hm)
    let y(v:Render S (m+1) N n):= river a! (m+1) n (W0 (m+1)) (post v)
    have hy (v:Render S (m+1) N n)(hv: Favored v): B (y v)=place a! m n (W0 m) (course hm v β):= (hB.ray (post v) (inside hv)).trans <| by unfold marble; rw [rule]; rfl
    have hz (v:Render S (m+1) N n)(hv: Favored v): F (y v)= ((surge hm v β-head S N m:ℝ):ℂ):= (hF.ray (post v) (inside hv)).trans <| by unfold Dales.flowing surge; rw [rule,add_sub_cancel_left]
    have hd: ‖y x-y x'‖= credit S (x-x'):= by
        unfold y; rw [← map_sub,eddies]; unfold post; simp only [Prod.snd_sub,Prod.fst_sub, sub_self, abs_zero]; exact max_eq_right (norm_nonneg _)
    have hA : credit S (course hm x β-course hm x' β)= ‖B (y x)-B (y x')‖:= by unfold credit; rw [hy _ he, hy _ hh,map_sub]
    rw [hA,← hd]; refine ⟨hB.bounds.2.2 _ (inside he) _ (inside hh),?_⟩
    have hX:= hF.bounds.2.2 (y x) (inside he) (y x') (inside hh); rw [hz _ he,hz _ hh,← Complex.ofReal_sub,sub_sub_sub_cancel_right,Complex.norm_real] at hX; exact hX
end YM.RGComparison.Core16.Unmarked
