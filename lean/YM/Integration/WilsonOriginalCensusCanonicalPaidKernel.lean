import YM.Integration.WilsonOriginalCensusCanonicalTranslatedPayer
import YM.Integration.WilsonReceivedChronologicalLastFlat
/-! The original two-flat physical payment for the measured canonical K edge. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalPaidKernel
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (base:m ≤ j) (cut:(j+1) < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q π Γ (Nat.le_succ_of_le base))
  (cal:Oak.Calendar R hk D Q π Γ Ψ (Nat.le_succ_of_le base) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {n:ℕ}(d:(Fin n)→ℕ)(q:(j:(Fin n))→Choice R d j)(hd:∀j,0 < d j)
  (y:(Fin n) → Lattice.Cover)(cells:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels (Fin n))(order shelf:ℕ)
local notation "o" => WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y cells

local notation "H" => Ψ ((j+1)+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))
local notation "M" => row R d q hd o scale
local notation "A" => room (Fin n)
local notation "K₀" => (fun _:(Fin n)=>(⊥:Submodule ℝ ℂ))
local notation "marks" => Stock.census (Fin n)
local notation "w₀" => (fun _:(Fin n)=>(1:ℝ))
local notation "C₀" => charge R d q scale w₀
local notation "g" => Coat.gStep (H).beta
local notation "D₀" => (∑v:(Fin n),d v)+1
local notation "χ" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "physical" => fun (x:Wallet (A))(U:Config G (R.family.side ((j+1)+1) per))=>
  ((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) x U)
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀)
  d order shelf op.count (j+1) (Nat.le_succ_of_le base) (physical)

local notation "S₀" => (fun _:(Fin n)=>max 1 (C₀))
local notation "e₀" => ((D₀)+5)*Fintype.card (Fin n)
local notation "rate" => fun s:(marks).Mode=>(R.alloy.B.a.clock.hatBeta (j+1))^(e₀)*Poly.toll (S₀) s
local notation "pupil" F:max => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le base) (F).op (F).lesson
  ahead (A) (F).model order (F).voter


local notation "voucher" F:max => WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead
  (A) (K₀) d order shelf op.count (physical) F (rate)
local notation "file" F:max B:max x:max => WilsonOriginalCensusCanonicalFiled.file
  R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) op ahead d q hd o order shelf F B x
local notation "pay" => Step.tape (Burn.horizon k+2)


open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open WilsonReceivedCanonicalSocketSeed (contact present)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)

open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
local notation "source" t:max => Source R hk D Q π Γ Ψ books base op lesson ahead d q hd y cells order shelf t


variable {S':Fin n→ℝ}{a':ℕ}(rows:∀i:ℕ,Config G (R.family.side i per)→Poly (Stock.census (Fin n)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
  {rentLimit:ℝ}(origin:WilsonOriginalCensusCanonicalFirstEdgePayer.Source R hk D Q π Γ Ψ books base op lesson ahead d q hd y cells order shelf rentLimit)(x:Wallet (WilsonOriginalMixedBlockRows.room (Fin n)))(same:∀U,(((Ψ ((j+1)+1)).eval U:ℝ):ℂ) • Poly.pass (Spill.Foundry.uncut (WilsonOriginalCensusCanonicalRows.row R d q hd (WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y cells) (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))) (Coat.gStep (Ψ ((j+1)+1)).beta) x U)=rows ((j+1)+1) U)

variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books
  (Nat.le_succ_of_le base) ahead (fun _:Fin n=>max 1 (WilsonOriginalCensusCanonicalRows.charge R d q (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))) (fun _:Fin n=>(1:ℝ)))) (((∑v:Fin n,d v)+1+5)*Fintype.card (Fin n)) (rows (j+1+1)))
  (adopts:upper=WilsonOriginalCensusCanonicalTranslatedPayer.named R hk D Q π Γ Ψ books base op lesson
    ahead d q hd y cells order shelf origin x (rows ((j+1)+1)) same)

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


local notation "peak" c:max l:max => 3*WilsonOriginalFullRosterBookedHearing.roof d d c l
local notation "Hhat" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "high" => upper.post
local notation "low" => lower.post
local notation "home" => ((high).passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "nh" => ((∑v:Fin n,upper.grades v)+1+5)*Fintype.card (Fin n)
local notation "nl" => ((∑v:Fin n,lower.grades v)+1+5)*Fintype.card (Fin n)
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
local notation "levelRank" => max ((∑v:Fin n,upper.grades v)+1) ((∑v:Fin n,lower.grades v)+1)
open WilsonOriginalFullRosterCouplingClock (work)
local notation "WD" f:max => WilsonOriginalFullRosterCouplingClock.wallet f
local notation "RD" d:max => WilsonOriginalFullRosterCouplingClock.raw d
open WilsonOriginalOccupiedCorridor
local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num : 0<(1:ℝ))
local notation "gAt" i:max => regulatorRun R.family N per i

open WilsonIndependentCollarOrbitalReception (relative)
open WilsonNeutralTwoPrintPathBoxHome (breadth)

include course cut adopts in
/-- Both older flat hearings of the declared binary edge retain its honest Haar numerator and actual hard return. -/
theorem original {s:(marks).Mode}{charges:(Fin n)→ℕ}{rentOrder h target:ℕ}{ε C:ℝ}
    (precision breadthCap lowOrder:ℕ)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn':∀v,0 ≤ S' v)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower charges rentOrder ε ((Hhat^precision)⁻¹) C)
    (pt:Fin n→Chamber)
    (tags:∀b:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per),(step R (j+1) b.val).Choices)
    {length:ℕ}{σ₀:ℝ}(L:Material R N (j+1) length d σ₀ (binder (coarse R (j+1) per) y))
    (active:Addressed y L (present L.tests))
    (matched:∀z S₁,output L.prior S₁ N z=fixed R d (fun v=>contact (L.tests v))
      pt N ((j+1)+1) (j+1) cells q z S₁)
    (lowPlaced:lower.post.passport=port (coarse R (j+1) per) y)
    (lowNames:lower.post.modelIndex=((z:Multi.Hot (marks))×(words L z).Roster))(lowInk:HEq lower.post.model (mounts L))
    (graded:lower.grades=d)(wallet:lower.x=x)
    (positive:0<Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1)))
    (depth:2*(precision+1)≤target)(lowOrderEq:lower.order=lowOrder)
    (highCap:(peak charges target)≤order)(lowCap:(peak charges target)≤length)
    (lens:Fin n→ℕ)(matchedTests:L.tests=lens)
    (menu:WilsonOriginalCensusCanonicalRelativePeriodSchedule.Appointment R simple d lens pt charges calendar.tube order lowOrder target precision depth)
    (go:menu.first≤j+1)(board:menu.period (j+1) breadthCap≤per)
    (near:∀t:Multi.Hot (marks), t.val.val⊆s.val→
      breadth t.val.val (calendar.front t) 0 (relative t.val.val (calendar.front t) y)≤breadthCap)
    (budget:2 ≤ C)(eps:ε ≤ 1){b K:ℕ}(floor:m ≤ b)(older:b ≤ j+1)(finer:j+1+1 ≤ K)(admitted:K ≤ N)
    (loadN cost P f gradeBudget:ℕ)(count:s.val.card ≤ loadN)(tariff:fee charges s ≤ f)(grade:(levelRank) ≤ gradeBudget)
    (period:R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (start:(eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original R simple loadN cost P f gradeBudget C
      (zero_le_two.trans budget))).choose ≤ b)
    (prior:work loadN P f gradeBudget+1+(WD f).pole+1 ≤ rentOrder)
    (shape:h=WilsonOriginalMountedRegularFare.crop (work loadN P f gradeBudget+1+(WD f).pole+(RD gradeBudget).pole) (gAt b))
    (jetOrder:work loadN P f gradeBudget+1+1≤precision)
    (support:(R.family.path.levels.budget (j+1)).supportExponent=100)
    (p:ℕ){tol:ℝ}(tp:0 < tol)(reserve:work loadN P f gradeBudget+2 ≤ p)
    (aged:WilsonOriginalMountedFailedHalo.first R simple loadN
      (Nat.cast_nonneg (work loadN P f gradeBudget+1+(WD f).pole+(RD gradeBudget).pole)) tp.le ≤ b)
    (atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (WilsonOriginalFullRosterBookedHearing.roof upper.grades lower.grades charges target) (Fintype.card (Fin n)) ≤ j)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (mature:WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1)
    (past:b < j+1)
    {u:ℕ}(mu:m ≤ u)(ub:u ≤ b)(fixed:WilsonSingleHardRadius.first R simple ≤ u)
    (narrow:upper.shelf ≤ R.alloy.B.a.clock.J (j+1))(load:(high).op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ j+1)(more:ready (high).op.count ≤ j+1)
    (wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ j+1)
    (neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ j+1)
    (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(qc:ℕ)
    (hardFloor:6*upper.seats ≤ R.alloy.B.a.clock.J (j+1))(hardDeep:2*(qc+1)+8 ≤ upper.order)(hardAge:qc+4 ≤ 3*k+2)
    {err:ℝ}(ep:0<err)(rented:err*(Coat.gStep (R.family.path.rep N per (j+1+1)).beta)^qc ≤ 1)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple (high).op.count qc upper.order k hardDeep hardAge ep ≤ j+1)
    (np:0<loadN)(stage:∀l,b ≤ l → loadN ≤ R.alloy.B.a.clock.J l)(load_ok:∀t:(marks).Mode,t.val.card ≤ loadN)
    (cap:∀l,b ≤ l → LocalComparison.forcedDivisor R.family l ≤ 1)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(atHome:center∈Z)
    (resident:∀v∈s.val,sites R (home) past.le v∈Z)
    (size drift:ℕ)(E η:ℝ)(ep₀:0<η)(E0:0≤E)
    (enclosed:coverNumber (Ψ b).p.B Z ≤ size)(reg:(Ψ b).p.supportExponent=100)
    (room:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple 0 (by norm_num:0<(1:ℝ)))).choose ≤ b)
    (late:(eventually_atTop.mp (WilsonOriginalOccupiedOpticalRate.original R simple loadN drift
       (2*s.val.card+((e₀)+∑v∈s.val,charges v)) P E E0 η ep₀)).choose ≤ (j+1)-1)
    (span:(((j+1)-b:ℕ):ℝ)≤E*(1+Real.log Hhat)^drift):
    WilsonReceivedChronologicalTwoFlatSale.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower u b s P size η ∧
    ∀v,u≤v→v≤b→WilsonReceivedChronologicalLastFlat.Ticket (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u b v s P size η ∧
      ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤
        WilsonReceivedChronologicalLastFlat.wage s P size η*(gAt b)^P:=by
  let front (t:Multi.Hot (marks)):t.val.val:=⟨calendar.front t,calendar.inside t⟩
  have bought:=WilsonOriginalCensusCanonicalTranslatedPayer.hearing R simple hk D Q π Γ Ψ course books base cut
    op lesson ahead d q hd y cells order shelf (rows (j+1)) lower origin pt x (rows ((j+1)+1)) same tags L active
    matched lowPlaced lowNames lowInk graded wallet positive s front charges calendar.tube target precision breadthCap
    lowOrder depth lowOrderEq highCap lowCap lens matchedTests menu go board near
  have gp:0≤gAt (j+1+1):=(ActualRunKernelPackets.regulator_pos R N per (j+1+1) cut).le
  have jets:((Hhat^precision)⁻¹)≤C*(gAt (j+1+1))^(work loadN P f gradeBudget+1+1):=
    (bought.1 _ jetOrder).trans (le_mul_of_one_le_left (pow_nonneg gp _) (one_le_two.trans budget))
  have nn:∀v,0≤(S₀) v:=fun _=>zero_le_one.trans (le_max_left _ _)
  let FaceAt (U:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base)
      ahead (S₀) (e₀) (rows (j+1+1)))(t:Multi.Hot (marks)):=WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ
      books base ahead (rows (j+1+1)) (rows (j+1)) U lower t (calendar.front t) charges calendar.tube target ((Hhat^precision)⁻¹)
  have seen (t:Multi.Hot (marks))(st:t.val.val⊆s.val):FaceAt upper t:=
    Eq.mpr (congrArg (fun U=>FaceAt U t) adopts) (bought.2 t st)
  have sale:WilsonReceivedChronologicalTwoFlatSale.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower u b s P size η:=
    .issued (h:=h) course cut way pass month hospital warm nn nn' calendar seen budget eps floor older finer admitted
      loadN cost f gradeBudget count tariff grade period start prior shape jets support p tp reserve aged
      atStation section_ group ticket mature failure past mu ub fixed narrow load one more wide neighbor
      capture qc hardFloor hardDeep hardAge ep rented opened np stage load_ok cap Z center atHome resident
      drift E ep₀ E0 enclosed reg room late span
  refine ⟨sale,?_⟩
  intro v uv vb
  exact ⟨Or.inl ⟨uv,vb,⟨base,(S₀),S',(e₀),a',upper,lower,sale⟩⟩,
    WilsonReceivedChronologicalTwoFlatSale.paid R simple hk D Q π Γ Ψ books base ahead rows upper lower sale uv vb⟩

end YM.Integration.WilsonOriginalCensusCanonicalPaidKernel
end
