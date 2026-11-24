import YM.QuadraticLocal.Campaign.Elixir
import YM.QuadraticLocal.Mentor.Tuition
import YM.QuadraticLocal.View
import YM.RemainderComparison.Gear.Class
/-!
# Institutions clock purchases for all finite local admission shapes

 Pre and post run authorization tied to the certified Portal.Actor.R stencil x. These
 lemmas allow purchasing it through `Legato.LawScroll`, Lookup x, flags, wallets etc after
 pre-block ratio and geometry buy. Stepwise growth costs as in Y(x)=min(flow of log, small variable
 power). Need to pick ALL reciprocals once before occupancy.World.Move Book.Frame and supply
 true window assumptions on each path.

 Page fields for a given stage (pair y,x) and fixed shape.Sequent: Order, replication count cap
 on monomial sizes, toll horizon etc. One envelope measure buys posts at EVERY κ Option Ticket and
 Holder Roll. Public Lean arithmetic here doesn't decide representation or lens count. Need each
 marker purchase.Owner budget & support.Height.T Θ with independent tests; no volume weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.MintClock
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
-- φ and ℓ omitted from struct to keep equality interfaces fixed in pre-L, reserve separate
structure Page where
   cap : ℕ
   order : ℕ
   rank : ℕ
   depth : ℕ
   halo : ℕ
   a : ℝ
   b : ℝ
   c : ℝ
   tol : ℝ
   height : ℝ→ℝ
   payroll : ℝ→ℝ
   supervisor : ℝ→ℝ

namespace Page
variable (G: Gauge) (D:Side) (P:Page) (u:ℝ)
def occupancy := Radii.occupancy P.halo P.cap P.depth
def span (B:ℕ) := Radii.survey P.halo P.cap P.depth B
def reach (B:ℕ) := Radii.window P.halo P.cap P.depth B
def helm (B:ℕ) := 2*Trio.base P.occupancy B
def cover (P:Page):= Trio.coverTicket P.occupancy
local notation "Z"=> P.occupancy
structure Eligible : Prop where
    well : 0<P.tol
    sound : P.tol ≤ 1/2
    enough : P.order+1 ≤ P.depth
    paid : RemainderComparison.Reserve G D P.height
    height_p x : 0< P.height x
    offered : RemainderComparison.Reserve G D P.payroll
    swept : RemainderComparison.Reserve G D P.supervisor
    lines : Width.Memento P.cap D P.a P.b P.c
    length : 2*Earn.Cable.links ≤ D.val
set_option quotPrecheck false
-- local attendance ticket
abbrev precision := Tuition.need P.order P.tol
abbrev fidelity := (Pressure.betaF G u D)^(Tuition.need P.order P.tol)
local notation "K"=> fun x=> Pressure.betaF G x D
local notation "Q"=> Delay.fineMonitor G D
local notation "Y"=> fun x=> P.fidelity G D x -- check dot
local notation "D'"=> D.val
local notation "F"=> radiusB u
abbrev temperature (x:ℝ) := 4*Delay.fineMonitor G D x
def computes : Earnings :=
   ⟨P.cap,P.order,P.depth,P.rank,P.a,P.b,P.c,P.height u,fidelity G D P u,P.supervisor u,P.payroll u,temperature G D u,P.a/4,temperature G D u,P.b/4,P.span F,P.helm F,P.cover⟩
local notation "Dt"=> P.computes G D u
local notation "y_"=> ( gStep (K u))
-- point flags as needed later. Radius assumptions already required by Π schedule. Hidden value β', chart. etc
abbrev enclosure (p:Stage) (q: BudgetPoint) (B:ℕ)(θ:ℝ):Prop:= Time.Same p q ∧ q.B=B ∧ q.threshold ≤ θ
-- arysize arithmetic for sectors
variable (hP:Eligible G D P)
lemma roof (b:ℕ)(hb:0<b): P.helm b≤ Trio.maxFixed P.occupancy*b:= Trio.roof _ _ hb
lemma coverCaps (x:Site D)(H:ℕ)(hb:0<H) : (coverNumber H (Animals.neighbors (P.helm H) x):ℝ)≤ P.cover:=by
   unfold cover Trio.coverTicket; apply Nat.cast_le.mpr; rw [two_mul (Trio.maxFixed Z)]; exact Trio.scaleMeters Z H hb x _ le_rfl
include hP
lemma frame (B T:ℕ)(hb:0<B)(h:T≤2*B)(hq:2*Cable.links ≤ B) : Width.fuelCuts D T (P.span B) B (P.helm B):=by
   have hr:5*B≤ P.span B:= Radii.first P.halo P.cap P.depth B; have he : P.span B ≤ P.reach B:= Radii.second ..
   let z:= P.reach B; have hp : (z*2)+1 ≤ Trio.base P.occupancy B:=by rw [mul_comm z]; exact (Radii.side P.halo P.cap P.depth B hb).2.1
   have hδ₀ : (2*Cable.links) *(T/D.val) ≤ T:= le_trans (Nat.mul_le_mul_right _ hP.length) (Nat.mul_div_le T D.val) -- lemma mul_div maybe order
   unfold Width.fuelCuts; rw [Nat.mul_add (2*Cable.links), Nat.mul_one]; unfold Page.helm; omega -- P.occupancy etc
lemma climate {x:ℝ}(hx:0 < Pressure.betaF G x D) (β:ℝ)(hv:inBand (betaF G x D) β) (t:ℝ)(ht:t ≤ 2*Pressure.fiery G x D): t ≤ gStep β * temperature G D x:= ht.trans (show 2*_ ≤ _ from by
    have ht: gStep (Pressure.betaF G x D)/2≤gStep β:= (band_gap _ β hx hv).1; change 2*(gStep (Pressure.betaF G x D) * Q x) ≤ _; unfold temperature; linarith only [mul_le_mul_of_nonneg_right ht (Delay.monitor_pos G D x).le])
-- Pose.BP. Tracker.Year.Run receipts
end Page
end YM.QuadraticLocal.MintClock
