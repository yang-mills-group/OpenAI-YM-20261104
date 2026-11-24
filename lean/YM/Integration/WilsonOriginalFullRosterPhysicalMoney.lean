import YM.Integration.WilsonOriginalFullRosterFiledHearing
import YM.Integration.WilsonOriginalCensusChronologicalMoney

/-! Financial stock of the two actual compact prints used in the common-cluster Wilson return. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterPhysicalMoney
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


def Accounts {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
    (F:WilsonOriginalMountedRegular.Filing R (vac) (upper.appointment.row upper.x) (lower.law lower.x) s):Prop:=
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
    F.W=W ∧ F.rent=rent ∧ F.gross=gross ∧ F.M=M ∧ F.α=(vac).p.supportExponent+1+1 ∧ F.h=h ∧ F.δ=δ

local notation "both" => roster (stamped) (low).model
local notation "wages" => sides (w₂) (low).w
local notation "costs" => sides (budgetR R (j+1)) (low).cost
local notation "degrees" => sides upper.grades lower.grades
local notation "orders" => sides upper.order lower.order

theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
    (budget:2 ≤ C)(small:regulatorRun R.family N per (j+1) ≤ 1)
    (cooled:(1+ε)*(regulatorRun R.family N per (j+1+1))^q ≤ 1):
    let g:=regulatorRun R.family N per (j+1)
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (upper.appointment.row upper.x) (lower.law lower.x) s,
      Accounts R simple hk D Q π Γ Ψ books base ahead rows upper lower course live way pass month hospital read F ∧
      F.W ≤ C*H^(fee charges s) ∧ F.gross ≤ C*H^2*(g⁻¹)^(rank) ∧ F.M ≤ C*H^(fee charges s+2)*(g⁻¹)^(rank) ∧
      F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q:=by
  intro g
  have upper_le (t:(marks).Mode):H^a*Poly.toll S t ≤ H^(nh)*Poly.toll S t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed (j+1)).le read.high_degree)
      (Finset.prod_nonneg fun v _=>nn v)
  have lower_le (t:(marks).Mode):(R.alloy.B.a.clock.hatBeta j)^a'*Poly.toll S' t ≤
      (R.alloy.B.a.clock.hatBeta j)^(nl)*Poly.toll S' t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed j).le read.low_degree)
      (Finset.prod_nonneg fun v _=>nn' v)
  have booked (t:(marks).Mode):=WilsonOriginalCensusPostedWages.original R simple hk D Q π Γ Ψ books base ahead
    (actors) (nulls) (actors) (nulls) upper.grades lower.grades upper.order upper.shelf upper.seats
    lower.order lower.shelf lower.seats upper.law lower.law (high) (low) upper.appointment lower.appointment
    upper.x lower.x t S S' charges nn nn' upper_le lower_le read.high_wage read.low_wage read.income
  have posH:0<H:=zero_lt_one.trans (R.alloy.B.a.fits.delayed (j+1))
  have dollars:budgetR R (j+1)≤H:=(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose_spec (j+1) read.income
  have earned:0 ≤ budgetR R (j+1):=zero_le_one.trans (budget_pos R)
  have allowance:0<(Ω)^6:=pow_pos (zero_lt_one.trans_le (high).issued.Waffle.cool) 6
  have entry:=course.1.walk (j+1) (Nat.le_succ_of_le base) live.le
  have thermal:H/2 ≤ (vac).beta:=by
    rw [entry.beta]
    exact (R.makes.wilson.represents N per (j+1) live.le).band.1
  have bp:0<(vac).beta:=lt_of_lt_of_le (by positivity) thermal
  have gp:0<(gc):=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have positive (b:Bool):∀v,0<(wages) b v:=by
    cases b
    · exact fun v=>div_pos ((high).salary.positive v) allowance
    · exact (low).salary.positive
  have funds (b:Bool):0 ≤ (costs) b:=by
    cases b
    · exact earned
    · exact budget_nonneg ((low).salary.suggests 0)
  have tests (t:Hot (marks))(ht:t.val.val⊆s.val):=by
    let fin:=fee charges t.val
    have current:=WilsonOriginalCensusTariff.measured gp posH bp thermal rfl (fin+1)
    have paid:WilsonEmittedJoinedFares.cash t.val (wages) (fun a=>if a then -1 else 1) (costs) ≤
        (2*((2:ℝ)^(fin+1)))*((gc)^(2*(fin+1)))⁻¹:=by
      rw [mul_assoc]
      exact (booked t.val).2.2.trans (mul_le_mul_of_nonneg_left current (by norm_num))
    exact WilsonOriginalCensusFiledProbe.purchased (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests upper.x lower.x)
      (vac).p (fun _=>σ) (costs) (orders) (gc) t (read.front t) ((home) (read.front t)) read.tube _ _ _ _
      (read.jets t ht) (fun _=>read.width) funds positive (by positivity) paid
  have block:=WilsonOriginalPhysicalAngularFiling.original R simple hk D Q π Γ Ψ course books base live ahead
    (actors) (nulls) (actors) (nulls) upper.grades lower.grades upper.order upper.shelf upper.seats lower.order lower.shelf
    lower.seats upper.law lower.law (high) (low) upper.appointment lower.appointment way pass month hospital
    read.fits read.narrow read.load q read.deep read.aged read.eps_pos read.late warm read.depth read.shelved read.slots
    read.halo s upper.x lower.x h read.tube read.front read.inside read.placed read.delta_nn tests
  let sale:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le base) live ahead
    (actors) (nulls) upper.grades upper.order upper.shelf upper.seats upper.law (high) simple way pass month hospital
    read.fits read.narrow read.load q read.deep read.aged read.eps_pos read.late
  obtain ⟨F,_,_,alpha,ap,ap',reg,rent,gross,later,M,crop,quote,_⟩:=block
  have accounts:Accounts R simple hk D Q π Γ Ψ books base ahead rows upper lower course live way pass month hospital read F:=by
    refine ⟨ap,rent,gross,?_,alpha,crop,quote⟩
    rw [M,ap,ap',reg,rent,later]
  have head₀:0 ≤ sale.choose:=budget_nonneg (sale.choose_spec.2.1.suggests 0)
  have earned₁:Invoice.price (vac).p (fig).mist (upper.order+upper.shelf+1) (high).op.count
      ((vac).p.supportExponent+1+1) (fig).limitC G ≤ budgetR R (j+1):=(high).issued.Waffle.quote.trans (high).issued.Beamwork
  have salaried:F.regular ≤ H^2:=by
    rw [reg,pow_two]
    exact mul_le_mul (earned₁.trans dollars) (sale.choose_spec.1.trans dollars) head₀ posH.le
  have pupil:=WilsonOriginalCensusFilingIncome.lower R hk D Q π Γ Ψ course books base live ahead (actors) (nulls)
    lower.grades lower.order lower.shelf lower.seats lower.law (low) warm read.depth read.shelved read.slots
  have b₂:=mul_le_mul pupil ((low).affordable.trans (inv_le_one_of_one_le₀ (low).issued.Waffle.cool))
    (budget_nonneg ((low).salary.suggests 0)) posH.le
  rw [mul_one] at b₂
  have same:(gc)=g:=by rw [entry.beta];rfl
  have raw:F.gross ≤ (2^(upper.order+upper.shelf+1)/g^((∑v:V,upper.grades v)+1))*H^2:=by
    rw [gross,←same]
    exact mul_le_mul_of_nonneg_left (reg.symm.trans_le salaried) (by positivity)
  have fresh:F.nextGross ≤ (2^(lower.order+lower.shelf+1)/g^((∑v:V,lower.grades v)+1))*H:=by
    rw [later,←same]
    exact mul_le_mul_of_nonneg_left b₂ (by positivity)
  have scaled:1 ≤ 8*(budgetR R (j+1))^(high).op.count:=by
    have one:=one_le_pow₀ (budget_pos R (i:=j+1)) (n:=(high).op.count)
    linarith only [one]
  have rest:(high).rent ≤ (regulatorRun R.family N per (j+1+1))^q:=by
    by_cases pos:0 ≤ (high).rent
    · exact (le_mul_of_one_le_left pos scaled).trans read.high_rent
    · exact (le_of_not_ge pos).trans (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have spent:F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q:=by
    rw [rent,add_mul,one_mul]
    exact add_le_add rest le_rfl
  have gp₀:0<g:=by rw [←same];exact gp
  obtain ⟨wallet,rawPay,complete⟩:=WilsonOriginalFiledClockMoney.original F (fee charges s) ((∑v:V,upper.grades v)+1)
    ((∑v:V,lower.grades v)+1) (R.alloy.B.a.fits.delayed (j+1)).le gp₀ small read.upper_pole read.lower_pole
    budget (ap.trans_le (booked s).1) (ap'.trans_le (booked s).2.1) salaried (spent.trans cooled) raw fresh M
  exact ⟨F,accounts,wallet,rawPay,complete,spent⟩

end YM.Integration.WilsonOriginalFullRosterPhysicalMoney
end
