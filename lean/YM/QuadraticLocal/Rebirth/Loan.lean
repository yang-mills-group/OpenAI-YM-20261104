import YM.QuadraticLocal.Rebirth.House
import YM.QuadraticLocal.Union.Commit
/-!
# Authorize the birth of every admitted step with chart horizon from the formal income.
 Carries calibration estimate ALL signed discrepancies at actor beta, independently post.actor geometry; actual couplings not re-selected for warm solver.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PositionX.Jet Extra.Iteration
open AllOrder AllOrder.Catch AllOrder.Catch.Clock AllOrder.Wheel AllOrder.Transit
open AllOrder.Rosary.Repair PostP AllOrder.Wheel.Ride
open Coat Next.Scheduling Next.Scheduling.Clock AllOrder.Floe
open Step Step.PlanV
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G: Gauge} {X: Metals G}
variable (D:RG.Supply.Rolls X.p)(R: Roots (G:=G) X.p.profile X.K X.p.kernel)
variable (x y:ℕ)(hx:4≤ x) {k:ℕ}
set_option quotPrecheck false
local notation "ρ"=> (Burn.horizon k)
local notation "L"=> D.L x
local notation "H"=> (fun t=> betaF G t (D.L x))
local notation "B"=> X.p.profile y
local notation "F'" => ( fun ξ:ℝ=> Pair.Note D R x y hx (q:=k) ξ )
local notation "N" => ρ+2
local notation "E"=> Aux.fare G (D.L x)
local notation "Z₁"=> (E).stage F'
variable (F: Income D R x y hx (Burn.horizon k))
open RemainderComparison
namespace Scholar
open ThroughLaunch Pane AllOrder.Ink AllOrder.Ink.Money Rebirth.Chart
local notation "I"=> Card D R x y hx ρ
local notation "Ξ" t:max=> strengthP (H t)
local notation "T"=> ( Predicted D R x y hx F )
open RG.Supply Mentor PriceCompiler

local notation "w"=> (MintClock.Page.reward)
local notation "κ"=> Beaming.grain y
local notation "s"=> House.amount D R x y hx F (y+1)
local notation "N0"=> (Burn.horizon k+1)
local notation "V"=> (fun d:ℕ=> Mentor.Tuition.need d (Tolerance y))
def rebate (t:ℝ) := ((Burn.horizon k+2:ℕ):ℝ)*( s t ) -- = (max order+1)*birth salary
structure Priced (t:ℝ) : Prop where
    quota : Scholar.rebate D R x y hx F t ≤ (MintClock.Page.reward (betaF G t (D.L x)) (Beaming.grain y))
    postBand (β:ℝ) : β∈ Set.Icc (t/2) (2*t) → inBand ( Pressure.betaF G t (D.L x) ) β
    earns (i:Predicted D R x y hx F t) (n e:ℕ)(z:ℤ) (hz : z∈ House.grammar (y+1)) (hr:n≤Burn.horizon k+1) (he:e≤ n) : |gStep (i.news.beta)^e * Balance.balance (F.issue i.news.token) ((F.sustenance.due i.news.token).1) (Burn.horizon k+2) z (gStep i.news.beta) (gStep i.post) (n-e)| ≤ (H t)^(V n)
local notation "h!"=> (Predicted D R x y hx F)
local notation "p" z:max i:max n:max e:max=> (Balance.balance (F.issue (Predicted.news i).token) ((F.sustenance.due (Predicted.news i).token).1) (Burn.horizon k+2) z (gStep (Predicted.news i).beta) (gStep (Predicted.post i)) (n-e))
local notation "Y"=> Econ -- placeholder
lemma ready : ∀ᶠ t:ℝ in atTop, Scholar.Priced D R x y hx F t:=by
   let H' n e (z:ℤ) (t:ℝ):= ∀ i:Predicted D R x y hx F t, |gStep i.news.beta^ (e:ℕ)* (p z i n e)|≤ (H t)^ (V n)
   have ht n z (hn : n≤ Burn.horizon k+1):∀ᶠ t:ℝ in atTop,∀ e∈ Finset.Iic n, H' n e z t := (eventually_all_finset (Finset.Iic n)).2 (fun e he=> by
      have h₀ := ( Predicted.census D R x y hx F z n e hn (mem_Iic.mp he) ) (V n) (show graded (n+1)< Mentor.Tuition.need n (Tolerance y) from lt_add_of_pos_right _ (by unfold Tolerance; positivity)); exact (((E).everybody («V»:=T) _).mp h₀) ) -- cast args. parentheses.
   have hz := House.budgets D R x y hx F (y+1); have hZ := MintClock.Page.tender G (L) (by unfold Beaming.grain; positivity : 0<κ) _ (show Reserve G (L) (Scholar.rebate D R x y hx F) from (Reserve.const _).mul hz)
   let A:=G.slopeConstant*Real.log ((D.L x).val:ℝ); filter_upwards [hZ,eventually_ge_atTop (2*|A|), (eventually_all_finset ( Finset.Iic (Burn.horizon k+1) ) («p»:=fun n t=> ∀ z∈House.grammar (y+1),∀ e∈Finset.Iic n,H' n e z t)).2 (fun n hn=> (eventually_all_finset _).2 (fun z _=> ht n z (mem_Iic.mp hn)))] with t hp hA hH; refine ⟨hp,?_,fun i n e z he hn he' => hH _ ( mem_Iic.mpr hn ) z he e (mem_Iic.mpr he') i⟩
   intro pβ hg; change pβ∈ Set.Icc ((t+A)/4) (4*(t+A)); constructor <;> linarith [le_abs_self A, neg_abs_le A, hg.1,hg.2]
open Mentor
variable (K':R.Tab D) {Tp: Protection D} (W:Delays Tp)
variable (a b:ℕ)(Tt: Mentor.Opportunity x y)(κp: Mentor.Epoch R D x y Tt)
structure Month : Prop where
   coupons (x y:ℕ) (Tt: Mentor.Opportunity x y)(κp: Mentor.Epoch R D x y Tt) (t:ℝ): W.betaEntry x ≤ t→ Scholar.Priced D R x y κp.wants (Mentor.Epoch.data R D K' Tt κp) t
lemma season : ∃ y:Delays Tp,DelayLe W y ∧ ∀ z:Delays Tp, DelayLe y z → Scholar.Month D R K' z := by
 let f i j (t:ℝ):= ∀ (Tt: Mentor.Opportunity i j)(K:Mentor.Epoch R D i j Tt), Priced D R i j K.wants (Mentor.Epoch.data R D K' Tt K) t
 have ha i j:∀ᶠ t in atTop,f i j t:= eventually_all.mpr (fun r=> eventually_all.mpr (fun K=> Scholar.ready D R i j K.wants (Mentor.Epoch.data R D K' r K)))
 let pC i t:= ∀ j:ℕ, PriceCompiler.StepStages i j → f i j t
 obtain ⟨A,-,hA,h⟩:=collect_upper W.betaEntry pC (fun x=> (eventually_transitions x atTop _ (fun y _=> ha x y))); refine ⟨{W with betaEntry:=A},⟨ hA, le_rfl, le_rfl, le_rfl⟩,fun Y' hy=> ⟨fun x y r K t ht=> h x t ((hy.beta x).trans ht) y r.meet r K⟩⟩
open Legato.VowsR
variable (G)
def genesis (ψ:ℕ→ℕ) : LawScroll G ψ where
    clause (Y') D PP C R₀ q Wp Z Q₀ S R Yr K T' V':= Scholar.Month D R Yr V'
    permits := by
      intro S Tq R C E' h; refine ⟨(fun _=> (0:ℕ)),fun l hL D q Wp Z Q' S' he P T₀ Yr Book hP V'=>?_⟩; exact Scholar.season (X:=ThroughLaunch.currency S Tq l) D R Yr V'
end Scholar
end YM.QuadraticLocal.Rebirth
