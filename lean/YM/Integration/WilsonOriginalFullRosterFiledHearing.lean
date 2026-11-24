import YM.Integration.WilsonOriginalFullRosterBookedHearing
import YM.Integration.WilsonOriginalDatedCensusEdge

/-! The common-cluster ordinary return for the two appointed dates of one chronological programme. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterFiledHearing
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)
variable {S S': V → ℝ}{a a':ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
local notation "high" => upper.post
local notation "low" => lower.post
local notation "vac" => Ψ (j+1)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead (actors) (high).model upper.order (high).voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le base) (high).lesson
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
local notation "home" => ((high).passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gc" => Coat.gStep (vac).beta
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "nh" => ((∑v:V,upper.grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,lower.grades v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
local notation "rank" => max ((∑v:V,upper.grades v)+1) ((∑v:V,lower.grades v)+1)

open WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
local notation "gf" => Coat.gStep (Ψ (j+1+1)).beta
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
  (gf) (gc) (vac) (high).output
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le base) (high).op (high).lesson ahead upper.order upper.shelf
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead upper.order upper.shelf
local notation "w₂" => Stoop.radius (high).w ((Ω)^6)


/-- Exact sale at two independently filed dates. The amount uses their genuine aperture, rent,
    Gaussian re-stamp, occupied credit, quiet spring, and the measured older group field. -/
def Earned {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
    (p:ℕ)(tol:ℝ){i:ℕ}(older:i ≤ j+1)(U:Config G (R.family.side i per)):Prop:=
    let sale:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le base) live ahead
      (actors) (nulls) upper.grades upper.order upper.shelf upper.seats upper.law (high) simple way pass month hospital
      read.fits read.narrow read.load q read.deep read.aged read.eps_pos read.late
    let reg:=Invoice.price (vac).p (fig).mist (upper.order+upper.shelf+1) (high).op.count ((vac).p.supportExponent+1+1)
      (fig).limitC G*sale.choose
    let χ:=R.alloy.B.a.clock.hatBeta (j+1)
    let other:=((2:ℝ)^(lower.order+lower.shelf+1)/(gc)^((∑v:V,lower.grades v)+1))*
      (Invoice.price (vac).p (MintClock.Page.temperature G 1 χ) (lower.order+lower.shelf+1) (low).op.count
        ((vac).p.supportExponent+1) ((σ)/4) G*(low).cost)
    let rent:=(high).rent+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q
    let gross:=((2:ℝ)^(upper.order+upper.shelf+1)/(gc)^((∑ v:V,upper.grades v)+1))*reg
    let W:=WilsonOriginalCensusMount.aperture (w₂) s
    let W':=WilsonOriginalCensusMount.aperture (low).w s
    let M:=max (W*(reg+rent)) (W'*other)
    let span:=max (vac).p.B (reach (vac).p.B h)
    (carried).hard=(high).output.hard ∧
      ((upper.appointment.row upper.x).A.density (upper.appointment.row upper.x).x=
        LocalComparison.actualPush R.family N per (j+1) (rows (j+1+1))) ∧
      ‖WilsonOriginalJointTrialHearing.fee R N per U rows (j+1) s-
        WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) older Ψ (upper.appointment.row upper.x) s U‖ ≤
        WilsonOriginalOrdinaryFlatHulls.change s M (W*rent+W*((Real.exp (((vac).p.supportExponent+1+1)*h))⁻¹*gross)+δ)+
          (if i=j+1 then 0 else (2*WilsonOriginalOrdinaryFlatHulls.cost s M)*((s.val.card*(span+span+1)^4:ℕ):ℝ)*
            (4*Real.exp ((vac).p.supportExponent+2))*tol/χ^p*(Real.exp (WilsonOriginalDecoderSpring.bill
              (R.family.path.levels.clock.op i per) (R.family.path.β N per (i+1)) U))^2)

include rows simple in
/-- The ordinary Haar difference at the selected earlier field, after its complete genuine occupied
    contribution. Each dated integral here is paid on the original independent post and its own quiet. -/
theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
    (child:∀v,(low).passport.origin v=(home) v)
    (atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (WilsonOriginalFullRosterBookedHearing.roof upper.grades lower.grades charges target) (Fintype.card V) ≤ j)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (p:ℕ){tol:ℝ}(tp:0<tol)(mature:WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1)
    {i:ℕ}(floor:m ≤ i)(older:i ≤ j+1)(fixed:WilsonSingleHardRadius.first R simple ≤ i)
    (U:Config G (R.family.side i per))(clear:flags (Ψ i).p.threshold U=∅):
    Earned R simple hk D Q π Γ Ψ books base ahead rows upper lower course live way pass month hospital
      read p tol older U:=by
  have upper_le (t:(marks).Mode):H^a*Poly.toll S t ≤ H^(nh)*Poly.toll S t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed (j+1)).le read.high_degree)
      (Finset.prod_nonneg fun v _=>nn v)
  have lower_le (t:(marks).Mode):(R.alloy.B.a.clock.hatBeta j)^a'*Poly.toll S' t ≤
      (R.alloy.B.a.clock.hatBeta j)^(nl)*Poly.toll S' t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed j).le read.low_degree)
      (Finset.prod_nonneg fun v _=>nn' v)
  have bought:=WilsonOriginalFullRosterBookedHearing.original R simple hk D Q π Γ Ψ course books base live ahead
    (actors) (nulls) (actors) (nulls) upper.grades lower.grades upper.order upper.shelf upper.seats
    lower.order lower.shelf lower.seats upper.law lower.law (high) (low) upper.appointment lower.appointment
    way pass month hospital read.fits read.narrow read.load q read.deep read.aged read.eps_pos read.late
    child read.placed s upper.x lower.x read.tube read.front read.inside read.width S S' charges
    nn nn' upper_le lower_le read.high_wage read.low_wage read.income target atStation read.delta_nn read.jets
    warm read.depth read.shelved read.slots read.halo section_ group ticket h p tp mature failure floor older fixed U clear
  have available:=R.alloy.B.a.fits.mono (Nat.le_succ_of_le (Nat.le_succ_of_le base))
  have highOrder:upper.order ≤ R.alloy.B.a.clock.J (j+1+1):=read.fits.trans
    ((Nat.le_add_right (Burn.horizon k+1) 1).trans (hk.trans available))
  have upperPaid:=WilsonOriginalFreshPrintedGross.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le base)
    live ahead (actors) (nulls) upper.grades upper.order upper.shelf upper.seats upper.law (high) simple
    warm highOrder read.narrow read.load (Nat.le_succ_of_le read.halo)
  have lowerPaid:=WilsonOriginalFreshPrintedGross.original R hk D Q π Γ Ψ course books base (Nat.lt_of_succ_lt live)
    ahead (actors) (nulls) lower.grades lower.order lower.shelf lower.seats lower.law (low) simple
    warm read.depth read.shelved read.slots read.halo
  have hiInt:Integrable (rows (j+1+1)) (prior G _):=by
    rw [←upper.atInput,funext (upper.appointment.declared upper.x)]
    exact upperPaid.2.2 upper.x
  have loInt:Integrable (rows (j+1)) (prior G _):=by
    rw [←lower.atInput,funext (lower.appointment.declared lower.x)]
    exact lowerPaid.2.2 lower.x
  have inlet:=(WilsonOriginalDatedCensusInput.Filed.paid R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)) upper s).1
  have split:=WilsonOriginalOccupiedJointEdge.original R (marks) π Γ Ψ course floor older live
    (upper.appointment.row upper.x) rows inlet hiInt loInt s U
  refine ⟨bought.1,inlet,?_⟩
  have named:=congrArg (fun F=>WilsonOriginalOccupiedJointEdge.ordinary R (marks) Ψ (N:=N) older
    (upper.appointment.row upper.x) F s U) lower.atInput
  rw [split,add_sub_cancel_left,←named]
  exact bought.2.2

end YM.Integration.WilsonOriginalFullRosterFiledHearing
end
