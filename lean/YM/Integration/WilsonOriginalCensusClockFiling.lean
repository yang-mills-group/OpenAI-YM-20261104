import YM.Integration.WilsonOriginalFundedCensusFiling
import YM.Integration.WilsonOriginalFiledClockMoney

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusClockFiling
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
include simple course cut lowBook in
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j) (slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')
    (h:ℕ)(tube:LinkTube G)(front:Hot (marks)→V)(mem:∀t,front t∈t.val.val)

    (placed:((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2)
    (width:0<σ)(entered entered':V→ℝ)(charges:V→ℕ)(nn:∀v,0 ≤ entered v)(nn':∀v,0 ≤ entered' v)
    (upper:∀t,tariff t ≤ H^(nh)*Poly.toll entered t)(lower:∀t,tariff' t ≤ H₁^(nl)*Poly.toll entered' t)
    (fund:∀v,entered v ≤ H^(charges v))(fund':∀v,entered' v ≤ H^(charges v))
    (income:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (target:ℕ){δ:ℝ}(dp:0 ≤ δ)(read:∀t:Hot (marks),t.val.val⊆s.val→
      WilsonOriginalCensusFiledProbe.Reading (both) (degrees) (WilsonOriginalCensusAngularFace.tests x z) (vac).p
        (fun _=>σ) (orders) (gc) t (front t) ((home) (front t)) tube (2*((fee charges t.val)+1))
        target (2*((2:ℝ)^((fee charges t.val)+1))) δ)
    {C:ℝ}(base:2 ≤ C)(coverHi:(2:ℝ)^(order+shelf+1) ≤ C)(coverLo:(2:ℝ)^(order'+shelf'+1) ≤ C)
    (small:regulatorRun R.family N per (j+1) ≤ 1)
    (fresh:(8*(budgetR R (j+1))^high.op.count)*high.rent ≤ (regulatorRun R.family N per (j+1+1))^q)
    (cooled:(1+ε)*(regulatorRun R.family N per (j+1+1))^q ≤ 1):
    let d:=fee charges s
    let k₀:=max ((∑v:V,grades v)+1) ((∑v:V,grades' v)+1)
    let γ:=regulatorRun R.family N per (j+1)
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (highBook.row x) (lowerLaw z) s,
      F.α=(vac).p.supportExponent+1+1 ∧ F.W ≤ C*H^d ∧ F.gross ≤ C*H^2*(γ⁻¹)^k₀ ∧
      F.M ≤ C*H^(d+2)*(γ⁻¹)^k₀ ∧ F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q ∧
      F.h=h ∧ F.δ=δ ∧ F.w=(w₂) ∧ F.w'=low.w:=by
  intro d k₀ γ
  obtain ⟨F,wage,wage',strip,envelope,envelope',regular,spent,raw,raw',account,length,jets,_⟩ :=
    WilsonOriginalFundedCensusFiling.original R simple hk D Q π Γ Ψ course books lo cut ahead A K A' K' grades grades'
      order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook way pass month hospital
      fits narrow load q deep aged ep late warm depth shelved slots halo s x z h tube front mem placed width
      entered entered' charges nn nn' upper lower fund fund' income target dp read
  have actual:(gc)=γ:=by rw [(course.1.walk (j+1) (Nat.le_succ_of_le lo) cut.le).beta];rfl
  have posH:1 ≤ H:=le_of_lt (R.alloy.B.a.fits.delayed (j+1))
  have hot:0<γ:=by
    change 0<(Real.sqrt (R.family.path.β N per (j+1)))⁻¹
    have bnd: H/2 ≤ R.family.path.β N per (j+1):=(R.makes.wilson.represents N per (j+1) cut.le).band.1
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [posH,bnd]))
  have scale:1 ≤ 8*(budgetR R (j+1))^high.op.count:=by
    have wage0:=one_le_pow₀ (budget_pos R (i:=j+1)) (n:=high.op.count)
    linarith only [wage0]
  have prev:high.rent ≤ (regulatorRun R.family N per (j+1+1))^q:=by
    by_cases nn0:0 ≤ high.rent
    · exact ((le_mul_of_one_le_left nn0 scale).trans fresh)
    · exact (le_of_not_ge nn0).trans (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have bill:F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q:=by
    rw [spent,add_mul,one_mul]
    exact add_le_add prev le_rfl
  rw [actual] at raw raw'
  obtain ⟨paid,passed,complete⟩:=WilsonOriginalFiledClockMoney.original F d ((∑v:V,grades v)+1) ((∑v:V,grades' v)+1)
    posH hot small coverHi coverLo base envelope envelope' regular (bill.trans cooled) raw raw' account
  exact ⟨F,strip,paid,passed,complete,bill,length,jets,wage,wage'⟩

end YM.Integration.WilsonOriginalCensusClockFiling
end
