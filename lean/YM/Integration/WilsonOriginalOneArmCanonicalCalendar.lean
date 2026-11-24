import YM.Integration.WilsonOriginalOneArmCanonicalBook
import YM.Integration.WilsonOriginalCensusCanonicalPaidSpring
import YM.Integration.WilsonOriginalOneArmBoardPair
import YM.Integration.WilsonOriginalCensusCanonicalSalary

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmCanonicalCalendar
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


local notation "Hhat" => R.family.path.levels.clock.hatBeta (j+1)
local notation "σₗ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "clock" => R.alloy.B.a.clock
local notation "gAt" i:max => Pert.Asymptotics.regulatorRun R.family N per i

/-- Both incoming degrees and the genuine upper canonical salary are priced before
the physical cutoff. The lower keeps its actual posted wallet and site. -/
theorem original {S':Fin n→ℝ}{a':ℕ}(raw:Config G (R.family.side (j+1) per)→Poly (marks))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' raw)
  {rentLimit:ℝ}(origin:source rentLimit)(x:Wallet (A))
(inHigh:Config G (R.family.side (j+1+1) per)→Poly (marks))
  (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base)
    ahead (S₀) (e₀) inHigh)
  (same:∀U,(physical) x U=inHigh U)
  (registered:upper=WilsonOriginalCensusCanonicalTranslatedPayer.named R hk D Q π Γ Ψ books
    base op lesson ahead d q hd y cells order shelf origin x inHigh same)
    (rentOrder level:ℕ)(charges:Fin n→ℕ)(part:∀v,1≤charges v)
    (fit:order≤Burn.horizon k+1)(shelved:shelf≤(clock).J (j+1))(count:op.count≤Burn.horizon k+2)
    (depth:2*rentOrder+8≤order)(age:rentOrder+3≤3*k+2)
    (ready:WilsonReceivedMeasuredStampPrice.opening R simple rentOrder order k depth age (by norm_num:0<(1:ℝ))≤j+1)
    (loDepth:lower.order≤(clock).J (j+1))(loShelf:lower.shelf≤(clock).J j)(loSeats:lower.seats≤Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose≤j+1)
    (income:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose≤j+1)
    (upperWidth:scale≤1)
    (sold:(eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
      (max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1)))).choose≤j+1)
    (loDegree:a'≤((∑v:Fin n,lower.grades v)+1+5)*Fintype.card (Fin n))
    (loMoney:∀v,S' v≤(Hhat)^(charges v))(rent:rentLimit≤(gAt (j+1+1))^rentOrder)
    (loPlaced:lower.post.passport=port (coarse R (j+1) per) y)
    (tube:LinkTube G)(front:Multi.Hot (marks)→Fin n)(owns:∀s,front s∈s.val.val)
    (teacher:0<σₗ ∧ Real.exp ((σₗ)⁻¹^2)≤(Hhat) ∧
      ((Ψ (j+1)).p.supportExponent+2)*(((Ψ (j+1)).p.B:ℝ)⁻¹)≤(σₗ)/2 ∧
      (Real.sqrt (Ψ (j+1)).beta)⁻¹≤1/2 ∧ (Ψ (j+1)).p.B=Nat.ceil ((Real.log (Hhat))^2) ∧
      (Ψ (j+1)).p.supportExponent+2≤102):
    ∃cal:WilsonOriginalSparseCensusEdge.Calendar (S:=(S₀)) (S':=S') (a:=(e₀)) (a':=a') (V:=Fin n) (m:=m) (j:=j) (N:=N) (per:=per) (k:=k) R simple hk D Q π Γ Ψ books base ahead
      inHigh raw upper lower charges rentOrder 1 (((Hhat)^level)⁻¹)
      (max ((2:ℝ)^(order+shelf+1)) ((2:ℝ)^(lower.order+lower.shelf+1))),
      cal.tube=tube ∧ cal.front=front:=by
  obtain ⟨grade,order_,shelf_,seats,placedHigh,highCost⟩:=
    WilsonOriginalOneArmCanonicalBook.original R hk D Q π Γ Ψ books base op lesson ahead
      d q hd y cells order shelf x inHigh upper origin same registered
  have hp:1≤Hhat:=(R.alloy.B.a.fits.delayed (j+1)).le
  have cash:max 1 (C₀)≤Hhat:=by
    exact (WilsonOriginalCensusCanonicalSalary.bound R d q upperWidth).trans
      ((eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
        (max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1)))).choose_spec (j+1) sold)
  obtain ⟨width,cap,placed,cool,side,tax⟩:=teacher
  refine ⟨{
    fits := order_.le.trans fit
    narrow := shelf_.le.trans shelved
    load := seats.le.trans count
    deep := depth.trans order_.ge
    aged := age
    eps_pos := by norm_num
    late := by simpa only [order_] using ready
    depth := loDepth
    shelved := loShelf
    slots := lower.post.capacity.le.trans loSeats
    halo := halo
    placed := placed
    width := width
    high_degree := by rw [grade]
    low_degree := loDegree
    high_wage := fun v=>by
      change max 1 (C₀)≤(Hhat)^(charges v)
      calc
        max 1 (C₀)≤Hhat:=cash
        _=(Hhat)^1:=(pow_one _).symm
        _≤(Hhat)^(charges v):=pow_le_pow_right₀ hp (part v)
    low_wage := loMoney
    income := income
    tube := tube
    front := front
    inside := owns
    delta_nn := inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp) _)
    upper_pole := by rw [order_,shelf_];exact le_max_left _ _
    lower_pole := le_max_right _ _
    high_rent := ?_
    child := ?_
    small := cool
    side := side
    tax := tax
    reserve := cap},rfl,rfl⟩
  · simpa only [seats] using highCost.trans rent
  · intro v
    change lower.post.passport.origin v=(upper.post.passport.coarser (step R (j+1) per).ratio).origin v
    rw [loPlaced,placedHigh]
    change wrap (coarse R (j+1) per) (y v)=(step R (j+1) per).ratio.parent
      ((step R (j+1) per).ratio.assemble (wrap (coarse R (j+1) per) (y v),cells (j+1) v))
    exact (Ratio.assemble_parent (step R (j+1) per).ratio (wrap (coarse R (j+1) per) (y v),cells (j+1) v)).symm

end YM.Integration.WilsonOriginalOneArmCanonicalCalendar
end
