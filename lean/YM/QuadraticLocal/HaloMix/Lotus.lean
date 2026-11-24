import YM.QuadraticLocal.Perspective.Regency
/-!
# Purchase site-uniform pencil. Uses given Mentor.Salary education; buys
 additional geometry and rates before any instances. Constants don't depend
 on Census cardinality or count-per-law.C beyond any desired fixed Opportunity.
 Precedes all periods & volumes. Prices are ≤ powers of true Monitor and can
 shrink radii by that at ANY step independently of arity. Cumulative later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration
open ThroughLaunch Height Opera Boulevard Trio Slide Sienna Fare Lapis Coat
open Input Org Supply Roost Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Burn AllOrder.Ink AllOrder.Ink.Money
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Wheel
open AllOrder.Wheel.Ride AllOrder.Wheel.Ride.Pair AllOrder.Catch
open QuadraticLocal.Sunrise QuadraticLocal.Echo RemainderComparison
open Legato.VowsR
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace MintClock.Pavilion
variable {G:Gauge}
open Poetry.Agenda Earn QuadraticLocal.Mentor
variable {X : Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D)
open AnalyticBridge.VerifiedReset Mentor Offices
variable (Z:Targets X.p X.K) (ψ:ℕ→ℕ)(K0:Offices.Books R D Q ψ){P:Protection D} (V:Delays P)
variable {x y:ℕ}(h:Opportunity x y)
set_option quotPrecheck false
local notation "L"=> D.L x
local notation "A"=> K0.salary x y h
local notation "Ψ"=> (A).enroll
local notation "Γ"=> (A).price
local notation "η"=> (Z x y)
local notation "B'f"=> fun i=>betaF G i (D.L x)
local notation "YL"=> X.p.profile y
local notation "Πf"=> Spire.fees (D.L x) ((YL).supportExponent+1+1)
local notation "ζ"=> Fintype.card (Site (D.L x))
local notation "Ω"=> Delay.fineMonitor G

def front (G:Gauge)(D:Side)(X':Salary G D)(Y':Stage)(t:ℝ):ℝ:= (1+|Spire.fees D (Y'.supportExponent+1+1)|)+|X'.enroll t| * |X'.price t|
abbrev closedRoom (y:ℝ) := y^(-(2/3:ℝ))
abbrev raiseRoom (y:ℝ):= y^(-(1/2:ℝ))
structure Tennis (k:ℕ) (ξ:ℝ):Prop where
   now : front G (D.L x) (K0.salary x y h) (X.p.profile y) ξ ≤ (Delay.fineMonitor G (D.L x) ξ)^k
   horizon : (Delay.fineMonitor G (D.L x) ξ)^k ≤ Page.reward ( betaF G ξ (D.L x) ) (Beaming.grain y)
   cap : |(K0.salary x y h).enroll ξ| * closedRoom ( betaF G ξ (D.L x)) ≤ 1
   hectare : Halo.hike (Z x y) ξ (Fintype.card (Site (D.L x))) (4*(raiseRoom (B'f ξ))) ≤ Daisy.ribbon (Z x y) (D.L x) ξ
   positive : 1 < B'f ξ
structure Purchased : Prop where
  roll : ∀ x y (P: Opportunity x y), ∃ k,∀ t:ℝ,V.betaEntry x ≤ t → Tennis R D Q Z ψ K0 P k t

local notation "K" => Z x y
lemma hired : ∃ k, ∀ᶠ t:ℝ in atTop,Tennis R D Q Z ψ K0 h k t:=by
   have hF:=Reserve.add (Reserve.const (G:=G) («L»:=D.L x) (1+|Πf|)) ((A).hU.absolute.mul (A).hV.absolute)
   change Reserve G (D.L x) (front G (D.L x) (A) YL) at hF; obtain ⟨k,hk⟩:= hF
   let u(t:ℝ):=4*raiseRoom (B'f t)
   let Xf(t:ℝ):= Halo.hike (Z x y) t ζ (u t)
   let X'(t:ℝ):= |(K0.salary x y h).enroll t| * closedRoom (B'f t)
   have hX: Rate G L (0+ -(1/2)) Xf:= by
       let hx:= (Halo.hikes («L»:=L) (Z x y) (p:=fun _=>ζ) (Δ:=fun _=>4) (Reserve.const _) (Reserve.const _)).rate; let v t:=Halo.hike K t ζ 4; rw [show Xf=(fun i=>v i*raiseRoom (B'f i)) from funext fun i=> by unfold Xf u v Halo.hike; ring]; exact Rate.mul hx Rate.power
   have hX': Rate G L (0+ -(2/3)) X':= (A).hU.absolute.rate.mul Rate.power
   refine ⟨k,?_⟩
   filter_upwards [hk,Page.tender G L (by unfold Beaming.grain; positivity : 0<Beaming.grain y) _ (Reserve.pow Reserve.monitoring k),hX'.below (by norm_num) _ zero_lt_one,hX ((Z x y).rate) (by rw [zero_add]; exact (Z x y).start), (Work.E09.betaF_growth G L).eventually_gt_atTop 1] with t ht hx hz hB hp
   have hP:0< B'f t:= zero_lt_one.trans hp; refine ⟨(le_abs_self _).trans ht,hx,(le_abs_self _).trans hz,(le_abs_self (Xf t)).trans (hB.trans ?_), hp⟩
   let E:=(Z x y); unfold Daisy.ribbon ConnectedActivityE6.Target.goal; apply le_mul_of_one_le_right (Real.rpow_nonneg hP.le _) (Real.one_le_exp (mul_nonneg ?_ ?_)); · unfold ConnectedActivityE6.Target.relative; linarith only [(Z x y).usable,(Z x y).pos,(Z x y).bound]
   unfold Footprint.preCost; positivity
lemma builder : ∃ U:Delays P,DelayLe V U∧∀ v:Delays P,DelayLe U v→ Purchased R D Q Z ψ K0 v := by
 choose k hk using fun x y (r: Opportunity x y)=>hired R D Q Z ψ K0 r
 let f x y (r:Opportunity x y) (ξ:ℝ):= Tennis R D Q Z ψ K0 r (k x y r) ξ
 let u x ξ:= ∀ y (r : Opportunity x y), f x y r ξ
 obtain ⟨q,-,hq,hA⟩:= collect_upper V.betaEntry u (fun x=> (eventually_transitions x atTop _ (fun y _=> (show ∀ᶠ ξ in atTop,∀ r:Opportunity x y, f x y r ξ from Filter.eventually_all.mpr (hk x y)))).mono (fun z h y r=> h y r.meet r)); refine ⟨{V with betaEntry:= q}, ⟨hq,le_rfl,le_rfl,le_rfl⟩,fun v hv=>⟨fun x y r=> ⟨_, fun t ht=> hA x t ((hv.beta x).trans ht) y r ⟩⟩⟩
def Degree (u:Purchased R D Q Z ψ K0 V):= (u.roll _ _ h).choose
local notation "k"=> Degree R D Q Z ψ K0 V h
lemma live (u:Purchased R D Q Z ψ K0 V) (ξ:ℝ)(ht:V.betaEntry x ≤ ξ): Tennis R D Q Z ψ K0 h (k u) ξ:= ( u.roll _ _ h ).choose_spec ξ ht

variable (G) (hψ:splits ≤ ψ)
open YM.Precision
set_option linter.unusedVariables false in
def scroll : LawScroll G ψ where
    clause (E) D PP C R₀ q w Z Q₀ S R Y K' T' V:= Purchased (X:=E) R D Y C ψ K' V
    permits := fun s Tq R C E' _=> ⟨0, fun l hL D w q Z Q' S' _ P T₀ Y Book _ V=>builder (X:=ThroughLaunch.currency s Tq l) R D Y (show Targets _ _ from C) ψ Book V⟩
end MintClock.Pavilion
end YM.QuadraticLocal
