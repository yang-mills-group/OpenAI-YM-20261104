import YM.Qlocal.Arrival
import YM.Qlocal.Embedding
/-!
# Repeated real subset propagation. Uniform exact re-expression at each step
 on the alternative unmarked representation with both its `early` and its
 actual Move, chosen by WheelP on the fixed campaign. A fixed marker alphabet
 and any Ω including the entire product of independent unit tests. Each level
 consumes the Output with same toll decremented by the visible step ratio paid
 BEFORE L etc. The costs apply BEFORE x, also after @∞ tails. Program is also
 parametrized by a protocol for additional housing steps; not asserting on every
 extra property of a Taste. Witness always comes with **representation**, Lens
 communicates. Further open up to add stricter mark-mask upgrades etc. Need real
 initialized bandwidth or actual initialized Peak.Price ≤1 here, not deemed.
 Marker radii and envelope persistence T.S never changes coupling. Vascular.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Program
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z : ℕ} {δ r θ u v w E C : ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
local notation "I"=> (a).clock.J m
local notation "J"=> (a).clock.J (m+1)
local notation "S"=> (a).clock.op m p
local notation "x₀"=> (a).clock.hatBeta m
open Frigus Scale
variable (Y₀:Org.Bolt A) (η:ℕ→ℝ)(H T:ℕ→ℕ)

/-- Launch triple of hired calendar facts. -/
def booked (η:ℕ→ℝ)(H T:ℕ→ℕ): YM.Qlocal.Schedule.Goal G:=fun X D A F=> Scale.era η H T X D A F ∧ Schedule.runway η H X D A F ∧ WheelP.Station A F
lemma sold (g:G.Simple)(h:∀ i,0 < η i): Schedule.Obtainable (booked (G:=G) η H T):= (Scale.widely η H T h).also ((Schedule.purchased H h).also (Schedule.all_orders g))

variable (h : booked η H T X D A F)
/-- One schedule of finite stage fees chosen before queries/periods. -/
structure Camp where
 station : WheelP.Station A F
 port : Schedule.runway η H X D A F
 height : ℕ→ℕ
 height' : ℕ→ℕ
 credit : (m:ℕ)→ Holdings.Bauble G (D.L (A.B.a.clock.J (m+1)))
 coupons (m:ℕ) : Scale.Lease.Coupon F (η:=η) (T:=T) (height m) (height' m) (credit m)
include h
lemma supplier {d:ℕ→ℕ}(hf:∀ m,d m ≤ H (A.B.a.clock.J (m+1))) : ∃ K : Camp F η H T,K.height=d:=by
 obtain ⟨h0,hw,hK⟩:= h
 choose b V H using fun i:ℕ=> Scale.Lease.available F h0 (d i) (hf i)
 exact ⟨⟨hK,hw,d,b,V,H⟩,rfl⟩
omit h
variable {F η H T}
namespace Camp
open Scale
variable (Q : Camp F η H T)
include Q

def step (m:ℕ):= (surf (D.L (A.B.a.clock.J (m+1))) (Q.credit m) (X.p.profile (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m))^2
abbrev scale (Q:Camp F η H T)(m i:ℕ): ℝ:=∏ j∈Finset.Ico m i, Q.step j
variable (m)
local notation "t★"=> A.B.a.clock.hatBeta (m+1)
lemma fee : 1 ≤ Q.step m ∧ Q.step m ≤ Scale.drawer t★ ^2∧ ∀ β∈band A.B.a (m+1), Time.quoteHard A.B.a m F.book β ≤ hardcap A.B.a T m:= by
 obtain ⟨hq,hp,hX⟩:= (Scale.Lease.actual F η T (Q.credit m) (Q.coupons m)).2.2.1; refine ⟨one_le_pow₀ hq,?_,hX⟩; exact pow_le_pow_left₀ (zero_le_one.trans hq) hp _
lemma scaled (i):1 ≤ Q.scale m i:=one_le_prod (fun j _=>(Q.fee j).1)
variable {m}
open RG3
variable {Y₀}
-- State subset.
variable {R: (i:ℕ)→ RG.Rep G (A.B.a.S.side i p)}{P : ℕ→Floe.Layout G}{Γ : ℕ→ Floe.Pace.Coin}(p₀:JourneyK A F Y₀ P Γ z N p k R) -- `JourneyK`
    (o:(i:ℕ)→V→ Site (A.B.a.S.side i p)) (s:(i:ℕ)→ V→Support (A.B.a.S.side i p)) (u: V→ℝ) (c:B.Mode→ℝ) (j:ℕ) -- j top of interval
local notation "R★"=> fun i=> Taste Ω (o i) (R i) B
local notation "Ttl"=> rent u c
-- include addresses for labels and caption. Useful Lifetime.Z. Deletion lifts. Need for lift activation inclusion.
structure Agenda (z q:ℕ):Prop where
 mask :∀ i,z ≤ i → i< q → s i=StageArt.fly (A.B.a.clock.op i p).ratio ∘ s (i+1)
 root :∀ i,z ≤ i → i< q → o i=(A.B.a.clock.op i p).ratio.parent ∘ o (i+1)
-- lemma any predata extends down to 0 later.Design clients.
local notation "p!"=> Agenda -- help
variable {o s c} [Fintype V] [Nonempty Ω][Nonempty V]
variable (hC:Spirit c)
include hC
omit hC Q -- ensure only wanted

local notation "Θ"=> R m
local notation "Ψ"=> R (m+1)
local notation "σ"=> (S).ratio.parent ∘ o (m+1)
local notation "u★"=>fun m=> shift (Q.scale m j) u
local notation "c★"=> fun m=>rent (u★ m) c

private lemma recast {A₀:ℝ}{d:Set (ℕ×ℕ)} {p:Lattice.Side} {L: RG.Rep G p}{o o':V→Site p}(h:o'=o) {s:V→Support p}(v:B.Mode→ℝ)(U:Taste Ω o L B)(hR: RetainsDeclared d U s)(hv:Peak L o U v L.p.supportExponent A₀ E)
    (F: Ω → Config G p→Poly B)(hf:∀ x,(U.leaf x).density= F x) : ∃ Z:Taste Ω o' L B, RetainsDeclared d Z s ∧ Peak L o' Z v L.p.supportExponent A₀ E∧∀ x,(Z.leaf x).density= F x := by subst o'; exact ⟨_,hR,hv,hf⟩
variable (hS:Agenda (A:=A) o s z j)
variable (hu:∀ x,0 < u x)
include p₀ hC Q hu hS
lemma next (hb:j ≤ N)(hi:m < j)(he:z ≤ m) (Y:Taste Ω (o (m+1)) (R (m+1)) B)
    (hv:Peak (R (m+1)) (o (m+1)) Y (c★ (m+1)) (R (m+1)).p.supportExponent 1 1)
    (hd:∃ d,RetainsDeclared d Y (s (m+1))) : ∃ K:Taste Ω (o m) (R m) B, (∃ d, RetainsDeclared d K (s m)) ∧ Peak (R m) (o m) K (c★ m) (R m).p.supportExponent 1 (Time.quoteHard A.B.a m F.book (R (m+1)).beta)∧ ∀ x,(K.leaf x).density=(S).push ((Ψ).beta) (Y.leaf x).density:= by
 let Θ':= o; let v:= u★ (m+1); have hm := hi.trans_le hb; have hc := p₀.1.walk (m+1) (by omega) hm; have ha:= p₀.1.walk m he hm.le; have hκ : (Ψ).beta ∈ band a (m+1):= hc.beta.symm ▸ (Y₀.sticks N p|>.prices (m+1) (by omega) hm).2
 have hx : ∀ i,(Θ).eval i≠0:= fun i=> ha.view.symm ▸ Frigus.TimeP.positive_at Y₀ hm.le i |>.ne'
 obtain ⟨d,h⟩:= hd
 obtain ⟨K,hK,hT,hZ⟩:= Frigus.lands F hm hc.truep (p₀.1.visit m he hm) hκ hx η v Y hv h (Q.coupons m) (p₀.2 m he hm) Q.station Q.port hC (shift_pos (zero_lt_one.trans_le (Q.scaled _ _)) hu)
 have hY : shift (Q.step m) v = u★ m := by
    unfold v; rw [shift_chain]; congr 1; rw [mul_comm]; exact (Finset.prod_eq_prod_Ico_succ_bot hi (fun y=>Q.step y)).symm
 have ht' : Peak (R m) _ K (rent (u★ m) c) (Θ).p.supportExponent 1 (Time.quoteHard A.B.a m F.book (Ψ).beta):= hY ▸ hK -- correction expected syntax;
 obtain ⟨Z,hT,hZ,ht⟩:= recast (hS.root m he hi) (rent (u★ m) c) K hT ht' _ (fun x=>(hZ x).symm)
 refine ⟨Z,⟨(Declared (R m) (s m) B),?_⟩,hZ,ht⟩; rw [hS.mask m he hi]; exact hT
end Camp
end YM.Qlocal.Program
