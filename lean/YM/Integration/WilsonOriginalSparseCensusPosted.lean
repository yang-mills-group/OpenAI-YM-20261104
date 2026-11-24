import YM.Integration.WilsonOriginalSparseFiledJointSale
import YM.Integration.WilsonOriginalCensusMountedPupils

/-! The physical terminal, calendar, both numerical sources and their common child are
fixed. Their genuine combined expense and their two original angular allowances pay
the reading obtained from the bounded sparse directions at that very child. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseCensusPosted
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open Pert.Asymptotics
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ) (lo:m ≤ j) (cut:j+1 < N)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [Fintype V] [DecidableEq V] {X Y:V→Type}
  [∀v,AddCommGroup (X v)] [∀v,Module ℝ (X v)] [∀v,AddCommGroup (Y v)] [∀v,Module ℝ (Y v)]
  (A:∀v,Set (X v)) (K:∀v,Submodule ℝ (X v)) (A':∀v,Set (Y v)) (K':∀v,Submodule ℝ (Y v))
  (grades grades':V→ℕ)(order shelf seats order' shelf' seats':ℕ)
  (upperLaw:Wallet A → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))
  (lowerLaw:Wallet A' → Config G (R.family.side (j+1) per) → Poly (Stock.census V))
  (high:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades order shelf
    seats (j+1) (Nat.le_succ_of_le lo) upperLaw)
  (low:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A' K' grades' order' shelf' seats' j lo lowerLaw)
local notation "vac" => Ψ (j+1)
local notation "marks" => Stock.census V
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le lo)
  high.op high.lesson ahead A high.model order high.voter
local notation "Lu" => rendered (student) (vac).p (Coat.gStep (Ψ ((j+1)+1)).beta)
local notation "next" => rendered low.model (vac).p (Coat.gStep (vac).beta)
local notation "home" => (high.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
variable {tariff tariff':(Stock.census V).Mode→ℝ}
  (highBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books (Nat.le_succ_of_le lo) ahead
    A K grades order shelf seats upperLaw high tariff)
  (lowBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books lo ahead
    A' K' grades' order' shelf' seats' lowerLaw low tariff')


local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le lo) high.lesson
local notation "gf" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gc" => Coat.gStep (vac).beta
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
  (gf) (gc) (vac) high.output
local notation "L" => rendered (stamped) (vac).p (gc)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "w₂" => Stoop.radius high.w ((Ω)^6)

open WilsonOriginalCensusAngularFace
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "both" => roster (stamped) low.model
local notation "wages" => sides (w₂) low.w
local notation "costs" => sides (budgetR R (j+1)) low.cost
local notation "degrees" => sides grades grades'
local notation "orders" => sides order order'
local notation "loads" => sides high.op.count low.op.count
local notation "shelves" => sides shelf shelf'
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₁" => R.alloy.B.a.clock.hatBeta j
local notation "nh" => ((∑v:V,grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,grades' v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
open Comparison.Density.Mirrors
open WilsonOriginalSparseFiledNodalSale (seatsCost)
open WilsonOriginalSparseFiledRanks (hull)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram WilsonOriginalCensusPhysicalLoad

variable (tape:Finset Age) (x:Wallet A) (z:Wallet A')
variable (chosenMode:YM.Multi.Hot (Stock.census V))
variable (v:V) (inFare:V→ℕ) (tube:LinkTube G) (target:ℕ)
local notation "S₀" => (2*((fee inFare chosenMode.val)+1))
local notation "A₀" => (2*((2:ℝ)^((fee inFare chosenMode.val)+1)))
local notation "D₀" => WilsonOriginalCensusPhysicalLoad.rank (degrees)
local notation "pole₀" => WilsonOriginalCensusPhysicalLoad.head (degrees) chosenMode.val
local notation "height" => pole₀+WilsonOriginalCensusTariff.debit S₀ D₀+target
local notation "lag" => WilsonOriginalCensusPhysicalLoad.delay (degrees) chosenMode.val
local notation "nodeSlots" => Site (R.family.side (j+1) per) × Loc G 1
local notation "groupHigh" e:max y:max => (peek dvd_rfl (stamped) grades (π (j+1)) tape x e y).part chosenMode.val
local notation "groupLow" e:max y:max => (peek dvd_rfl low.model grades' (π (j+1)) tape z e y).part chosenMode.val

include simple course cut highBook lowBook
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order≤Burn.horizon k+1)(narrow:shelf≤R.alloy.B.a.clock.J (j+1))
    (load:high.op.count≤Burn.horizon k+2)(q:ℕ)(deep:2*q+8≤order)(aged:q+3≤3*k+2){η:ℝ}(ep:0<η)
    (starts:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep≤j+1)
    (child:∀u,low.passport.origin u=(home) u)(resident:v∈chosenMode.val.val)
    (entered entered':V→ℝ)(nn:∀u,0≤entered u)(nn':∀u,0≤entered' u)
    (upper:∀s,tariff s≤H^(nh)*Poly.toll entered s)(lower:∀s,tariff' s≤H₁^(nl)*Poly.toll entered' s)
    (fund:∀u,entered u≤H^(inFare u))(fund':∀u,entered' u≤H^(inFare u))
    (income:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose≤j+1)
    (legal:Legal tape (π (j+1)))(bnd:ℕ→ℕ→ℝ)(positive:∀e r,0≤bnd e r)
    (unit:∀e,e+pole₀<3*height → ‖groupHigh e 0-groupLow e 0‖≤bnd e 0)
    (nodes:∀e,e+pole₀<3*height → ∀r:ℕ,0<r → r≤e+pole₀ → ∀Z:Fin r→nodeSlots,
      (∀u,Z u∈hull G ((home) v) ((vac).p.B/32)) → ∀F c,
      let y:=WilsonOriginalSparsePeg.probe (e+pole₀) Z F c
      ‖groupHigh e y-groupLow e y‖≤bnd e r)
    (width:ℝ)(room:Room (vac).p (R.family.side (j+1) per) tube (vac).p.B width)
    (radius:0≤width)(held:width≤2*(gc)^(1/2:ℝ))(sigma_pos:0<σ)(small:(gc)≤1/2)
    (side:(vac).p.B=Nat.ceil ((Real.log H)^2))(tax:(vac).p.supportExponent+2≤102)
    (reserve:Real.exp (((σ)⁻¹)^2)≤H)(hot:Real.exp 1≤H)(saved:ℕ)
    (fixed:WilsonOriginalSparseFiledRosterCash.room G (3*height)≤H)
    (late:(512*((2*(1+((fee inFare chosenMode.val)+2)+saved):ℕ)+1:ℝ))^2≤Real.log H)
    (ε δ:ℝ)(eps:0≤ε)
    (total:∀e,e+pole₀<3*height → ((e+pole₀).factorial:ℝ)*
      (∑r∈range (e+pole₀+1),(seatsCost G ((vac).p.B/32) r*
        (WilsonOriginalSparseFiledNodes.factor (e+pole₀)*bnd e r)+2*(H^saved)⁻¹))≤ε)
    (begun:WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height (orders) lag H)
    (quote:(((gc)^pole₀)⁻¹*(groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
      (WilsonEmittedOutputPower.constant height+1)*(WilsonOriginalCensusFiledProbe.posted A₀ D₀)*(gc)^target≤δ):
    Nonempty (WilsonOriginalCensusFiledProbe.Reading (both) (degrees) (WilsonOriginalCensusAngularFace.tests x z)
      (vac).p (fun _=>σ) (orders) (gc) chosenMode v ((home) v) tube S₀ target A₀ δ):=by
  obtain ⟨arms,homes,_,_⟩:=WilsonOriginalCensusMountedPupils.original R simple hk D Q π Γ Ψ course books lo cut ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low
    way pass month hospital fits narrow load q deep aged ep starts child
  have booked:=WilsonOriginalCensusPostedWages.original R simple hk D Q π Γ Ψ books lo ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook
    x z chosenMode.val entered entered' inFare nn nn' upper lower fund fund' income
  have temperature:H/2≤(vac).beta ∧ (vac).beta≤2*H:=by
    rw [(course.1.walk (j+1) (Nat.le_succ_of_le lo) cut.le).beta]
    exact (R.makes.wilson.represents N per (j+1) cut.le).band
  refine ⟨?_⟩
  exact WilsonOriginalSparseFiledJointSale.original (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z)
    (vac).p (fun _=>σ) (costs) (orders) (gc) chosenMode v ((home) v) tube S₀ target A₀ δ
    (fun _=>π (j+1)) (fun _=>tape) (fun _=>legal) arms (fun _=>sigma_pos)
    (fun a=>(arms a).positive) resident (homes v) ((vac).p.B/32) bnd positive ε eps unit nodes
    width room radius held H (vac).beta temperature rfl small side tax (fun _=>reserve)
    (congrArg (fun m:ℕ=>m/32) side) hot (fun a=>budget_nonneg ((arms a).suggests 0))
    (fee inFare chosenMode.val) saved booked.2.2 fixed late total begun quote

end YM.Integration.WilsonOriginalSparseCensusPosted
end
