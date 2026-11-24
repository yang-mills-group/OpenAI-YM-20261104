import YM.Qlocal.Clock
import YM.Qlocal.Traction
/-! On the *real* sold nuclear path. Use ink charged winding (all k and component calls).
 Apply BindSum toward vacuum task. This file prices periodization error Fk vs canonical vacuum analytic
 packets grouping, not marked impulses (see separate purchase). Actual occupancy theorem includes Born pushes
 all forced. Does not assert smooth global log density in configs with flags. Model Loops and clipped
 priced separately. Finite order theta real numerical gating later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open Further.PhysicalPeriodLimitF933 PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Program Program.Camp Program.Certificate
variable {Ω V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge} {m k p N j k' z n l v : ℕ} {δ r θ u E C ℓ: ℝ}
open Primitives.TwoWave Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money
open Work.G05 Kinetic.Port Kinetic Binding
open Comparison.RG02.Bulk
open Org Floe Pace Step.PlanV
-- guard notation all dependent arguments fully (macro locality)
variable (X:Run G)
set_option quotPrecheck false
local notation "W"=> X.metals
local notation "D"=> X.rolls
local notation "A"=> X.alloy
local notation "C"=> X.family
local notation "Y"=> RunFormalChain.fromRun X
local notation "a"=> X.alloy.B.a
local notation "K"=> X.metals.p.kernel
local notation "J"=> X.alloy.B.a.clock.J (m+1)
local notation "J'"=> X.alloy.B.a.clock.J m
local notation "t₀"=> X.alloy.B.a.clock.adm (m+1)
local notation "κ"=> X.metals.p.profile
local notation "P"=> Mural.sheet X.metals.p X.rolls (X.alloy.B.a.clock.adm (m+1))
local notation "S"=> (a).clock.op m p
local notation "c"=> (a).S.side m p
local notation "f"=> (a).S.side (m+1) p
local notation "f₀"=> (κ J).clip
local notation "p₀"=> (κ J').clip
local notation "k₀"=> Burn.horizon k
local notation "Z"=> Age.scope (Burn.horizon k+2)
variable (R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel)(Q:R.Tab X.rolls)
local notation "I"=> Card D R J J' t₀ k₀
variable (w:ℕ→Floe.Layout G) (Γ:ℕ→ Floe.Pace.Coin) (x:(i:ℕ)→RG.Rep G (X.alloy.B.a.S.side i p))
    (h:JourneyK X.alloy X.kit X.T w Γ z N p k x)
    (he:m<N) (ht:z ≤ m)
variable (hd:Burn.horizon k+2 ≤ X.alloy.B.a.clock.J m) (D': Card X.rolls R (X.alloy.B.a.clock.J (m+1)) (X.alloy.B.a.clock.J m) (X.alloy.B.a.clock.adm (m+1)) (Burn.horizon k))
local notation "α₀"=> X.metals.O
local notation "ξ₀"=> X.metals.oga
local notation "F!"=> litP R A Q hd D'
lemma level_path (m n N:ℕ)(hk:m ≤ N):((C).path.rep N n m).path=X.alloy.B.kin.path N m∧ ((C).path.rep N n m).clip=(X.metals.p.profile (X.alloy.B.a.clock.J m)).clip:=by
 exact ⟨(Y).selected N n m hk,((Y).clips N n m hk).trans (congr_arg RG.Stage.clip (params_eq X.alloy.B.valid _))⟩ -- syntax
lemma dbind : ((S).patch=P)∧ (S).kernel=K:= by
 let y: (f).val=(c).val*((A).B.a.S.block m).val:= (a).S.oneStep m p|>.exact_size -- notation spaces
 exact ⟨ Plateau.Line.patch_here A y, X.alloy.B.valid.kernel⟩
include h he ht
lemma stout : Bid.Larger (G:=G) S:= by obtain ⟨V,H⟩:= h.2 m ht he; exact V.laws.data.room.larger
omit h he ht
variable [Fintype V]
-- words.Act.If query changes horizon, same path X. t chosen ∃ Service not pivot choices.
variable (T:Colors B G (X.family.side (m+1) p)) (F:Forest ((X.family.path.levels.clock.op m p).ratio)) (T':(X.family.path.levels.clock.op m p).Choices)
def sample (y:fieldDir G (X.family.side m p) 1) : LocalFormal.Datum X.family B:=⟨N,p,m,he,F,T',T,y⟩
-- tib price to real.ValenceL.Nick.Q lemma argument ordering F' lookup
local notation "δ'"=> dearth (F!).σ c
local notation "μ"=> (F!).revenue
local notation "Z'"=> rule (Coarse G) c
variable (hQ:Journey R X.alloy (N:=N) (m:=m) D')
local notation "M"=> (F!).presence
local notation "u'"=> (F!).tools
local notation "SH"=> Floe.Step.vista M D'
local notation "b'"=> (μ).b j D' c
set_option quotPrecheck false
local notation "x☆"=> (x m)
local notation "V₁"=> fun (v:Card D R J J' t₀ k₀)=> v.self.north
local notation "v★"=> prePhase P K f₀ α₀ V₁ (fun i:I=>i.self.paid) (F!).frame (fun i:I=>i.self.upCost) X.metals.oga (F!).tools (F!).efficient (Card.extra) (Step.tape (Burn.horizon k+2)) (audited D R J J' t₀)
include h he ht hQ
-- cast colors.W.Center.Lattice
variable (hT:T.vac=drawn D'.extra (Age.scope (Burn.horizon k+2)) (X.alloy.B.a.S.side (m+1) p)) (hJ:j ≤ l)
include hJ hT
/-- Fk prescription for vacuum including actual Datum at all periods. Complete NO recursioin yet: estimate for the ν.The winding not inferred for un-admitted virtual period; must call Z'.L.Vyx. -/
lemma enters (y: Z') : ↑(v★ D' j c y)=(sample X he T F T' 0|>.vacuumAction Y l) j (tint G _ (Kinetic.Port.exteriorL G c y)) := by
 have hn:Nonempty I:= ⟨D'⟩; let q:=(S).patch; exact Binding.clock P K f₀ α₀ V₁ (fun i:I=>i.self.paid) (F!).frame _ _ _ (F!).efficient Card.extra Z _ D' F T' ((Y).step N m p he) T hT j l hJ (dbind X (p:=p)).1 (dbind X (p:=p)).2 ((level_path X _ p N he).1.trans hQ.books.north.symm) ((level_path X _ p N he).2) (stout X w Γ x h he ht) y -- dot notation macro Y issue
lemma story (hh:j ≤ Burn.horizon k+2) :
    Prices (j+2) (b'*δ') (((fun y:Z'=> ((sample X he T F T' 0|>.vacuumAction Y l) j (tint G _ (Kinetic.Port.exteriorL G c y))).re)) - SH j c):= by
 let C':= (litP R A Q hd D'|>.revenue); have hp:Ad G P K c:= Wheel.Ride.scope_complete S (dbind X (p:=p)).1 (dbind X (p:=p)).2 (stout X w Γ x h he ht); let v := v★ D' j c
 have hc:Prices (j+2) ((C'.b j D' c)*dearth (F!).σ c) (v-SH j c):= ((C'.earns j D' hh).2 _ hp)
 refine Eq.mp ?_ hc
 apply congr_arg; apply congr_arg (· - (SH j c)); funext u; rw [← enters X R Q w Γ x h he ht hd D' T F T' hQ hT hJ u]; exact (Complex.ofReal_re _).symm -- xs name
end YM.Qlocal.Actual
