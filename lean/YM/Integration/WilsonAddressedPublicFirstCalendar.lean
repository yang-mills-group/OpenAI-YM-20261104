import YM.Integration.WilsonAddressedPublicSubmittedFiling
import YM.Integration.WilsonOriginalOneArmCanonicalCalendar
import YM.Integration.WilsonOriginalCensusCanonicalTranslatedPayer
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstCalendar
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
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonNeutralTwoPrintPathBoxHome (breadth)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)

open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
local notation "source" t:max => Source R hk D Q π Γ Ψ books base op lesson ahead d q hd y cells order shelf t



local notation "clock" => R.alloy.B.a.clock
local notation "Hhat" => (clock).hatBeta (j+1)
local notation "σₗ" => Poetry.Agenda.seed D φ (Burn.horizon k) ((clock).J (j+1))
local notation "sideₗ" => coarse R (j+1) per
local notation "geom" => binder (sideₗ) y
variable {rentLimit tol : ℝ}(origin : WilsonOriginalCensusCanonicalFirstEdgePayer.Source R hk D Q π Γ Ψ books base op lesson ahead d q hd y cells order shelf rentLimit) (x : Wallet (room (Fin n)))
  (rawHigh : Config G (R.family.side (j+1+1) per) → Marker.Poly (Stock.census (Fin n)))
  (same : ∀U, (((Ψ (j+1+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (row R d q hd (WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y cells) (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))) (Coat.gStep (Ψ (j+1+1)).beta) x U))=rawHigh U)
  (opL : Mentor.Opportunity (R.alloy.B.a.clock.J (j+1)) (R.alloy.B.a.clock.J j))
  (lessonL : Lesson (N:=N) R hk D Q π Γ base)
  (length lowOrder lowShelf : ℕ) (bills : Fin n → ℝ)
  (Mₗ : Material R N (j+1) length d (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))) (binder (coarse R (j+1) per) y))
local notation "high" => WilsonOriginalCensusCanonicalTranslatedPayer.named R hk D Q π Γ Ψ books base
  op lesson ahead d q hd y cells order shelf origin x rawHigh same
local notation "bill" => WilsonIndependentCollarMaterialWallet.bill Mₗ bills
local notation "lowCash" => fun v=>bills v*max 1 (WilsonOriginalMixedBlockBudget.roots
  (geom) (bill))
local notation "loRaw" => WilsonOriginalPhysicalFieldsAtBoard.printed (marks) (Ψ (j+1))
  (rendered (mounts Mₗ) (Ψ (j+1)).p (Coat.gStep (Ψ (j+1)).beta)) x
local notation "power₀" => ((∑v:Fin n,d v)+1+5)*Fintype.card (Fin n)
local notation "peak" c:max => 3*WilsonOriginalFullRosterBookedHearing.roof d d (fun _ : Fin n=>4) c
local notation "bound" => max ((2:ℝ)^(order+shelf+1)) ((2:ℝ)^(lowOrder+lowShelf+1))

include course cut in
theorem original (posted : WilsonOriginalFixedTestCensusFiledBook.Ready R hk D Q π Γ Ψ books base
      opL lessonL ahead (port (sideₗ) y) (geom) d lowOrder lowShelf length bills Mₗ tol)
    (submitted : ∀v, (lowCash) v ≤ (Hhat)^4)
    (pt : Fin n → Chamber) (lens : Fin n→ℕ) (test : Mₗ.tests=lens)
    (lives : Addressed y Mₗ (present Mₗ.tests))
    (fixed : ∀z S, output Mₗ.prior S N z=WilsonReceivedFixedDigitCanonical.fixed R d
      (fun v=>contact (Mₗ.tests v)) pt N (j+1+1) (j+1) cells q z S)
    (tags : ∀b:Covers R.family.path.levels.S (j+1) (sideₗ),(step R (j+1) b.val).Choices)
    (rentOrder precision target breadthCap : ℕ)
    (fit : order ≤ Burn.horizon k+1)(shelved : shelf ≤ (clock).J (j+1))
    (count : op.count ≤ Burn.horizon k+2)(depth : 2*rentOrder+8 ≤ order)(age : rentOrder+3 ≤ 3*k+2)
    (ready : WilsonReceivedMeasuredStampPrice.opening R simple rentOrder order k depth age
      (by norm_num:0<(1:ℝ)) ≤ j+1)
    (loDepth : lowOrder ≤ (clock).J (j+1))(loShelf : lowShelf ≤ (clock).J j)
    (loSeats : opL.count ≤ Burn.horizon k+2)
    (halo : (eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (income : (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (upperWidth : scale ≤ 1)
    (sold : (eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
      (max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1)))).choose ≤ j+1)
    (rent : rentLimit ≤ (Pert.Asymptotics.regulatorRun R.family N per (j+1+1))^rentOrder)
    (tube : LinkTube G)(front : (t:Multi.Hot (marks)) → t.val.val)
    (teacher : 0<σₗ ∧ Real.exp ((σₗ)⁻¹^2)≤(Hhat) ∧
      ((Ψ (j+1)).p.supportExponent+2)*(((Ψ (j+1)).p.B:ℝ)⁻¹)≤(σₗ)/2 ∧
      (Real.sqrt (Ψ (j+1)).beta)⁻¹≤1/2 ∧ (Ψ (j+1)).p.B=Nat.ceil ((Real.log (Hhat))^2) ∧
      (Ψ (j+1)).p.supportExponent+2≤102)
    (accuracy : 2*(precision+1) ≤ target) (highCap : peak target ≤ order)(lowCap : peak target ≤ length)
    (menu : WilsonOriginalCensusCanonicalRelativePeriodSchedule.Appointment R simple d lens pt
      (fun _ : Fin n=>4) tube order lowOrder target precision accuracy)
    (go : menu.first ≤ j+1)(board : menu.period (j+1) breadthCap ≤ per)
    (near : ∀t : Multi.Hot (marks), breadth t.val.val (front t).val 0
      (relative t.val.val (front t).val y) ≤ breadthCap) :
    ∃low : WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books base ahead
      (lowCash) (power₀) (loRaw),
      low.x=x ∧ low.grades=d ∧ low.order=lowOrder ∧ low.shelf=lowShelf ∧
      low.post.passport=port (sideₗ) y ∧
      ∃cal : WilsonOriginalSparseCensusEdge.Calendar R simple hk D Q π Γ Ψ books base ahead
          rawHigh (loRaw) (high) low (fun _ : Fin n=>4) rentOrder 1 (((Hhat)^precision)⁻¹) (max ((2:ℝ)^(order+shelf+1)) ((2:ℝ)^(low.order+low.shelf+1))),
        cal.tube=tube ∧ cal.front=(fun t=>(front t).val) ∧
        (∀w≤precision, ((Hhat)^precision)⁻¹ ≤ (Pert.Asymptotics.regulatorRun R.family N per (j+1+1))^w) ∧
        Nonempty (∀t : Multi.Hot (marks), WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ books base
          ahead rawHigh (loRaw) (high) low t (cal.front t) (fun _ : Fin n=>4) cal.tube target (((Hhat)^precision)⁻¹)) := by
  obtain ⟨_,_,_,_,_,_,wallet⟩ := posted
  obtain ⟨low,hx,hg,ho,hs,hn,_,_,site,names,ink,_,_,_⟩ := wallet x
  have degree : (power₀) ≤ ((∑v:Fin n,low.grades v)+1+5)*Fintype.card (Fin n) := by rw [hg]
  have sale := WilsonOriginalOneArmCanonicalCalendar.original R simple hk D Q π Γ Ψ books base op
    lesson ahead d q hd y cells order shelf (loRaw) low origin x rawHigh (high) same rfl
    rentOrder precision (fun _ : Fin n=>4) (fun _=>by decide) fit shelved count depth age ready
    (ho.le.trans loDepth) (hs.le.trans loShelf) (hn.le.trans loSeats) halo income upperWidth sold degree submitted
    rent site tube (fun t=>(front t).val) (fun t=>(front t).property) teacher
  obtain ⟨cal,tubeEq,frontEq⟩ := sale
  have first : ∀w≤precision, ((Hhat)^precision)⁻¹ ≤ (Pert.Asymptotics.regulatorRun R.family N per (j+1+1))^w :=
    menu.jets (j+1) go N per cut
  refine ⟨low,hx,hg,ho,hs,site,cal,?_,?_,first,?_⟩
  · exact tubeEq
  · exact frontEq
  · refine ⟨?_⟩
    intro t
    rw [tubeEq,frontEq]
    exact (WilsonOriginalCensusCanonicalTranslatedPayer.hearing R simple hk D Q π Γ Ψ course books base cut op
      lesson ahead d q hd y cells order shelf (loRaw) low origin pt x rawHigh same tags Mₗ lives
      fixed site names ink hg hx teacher.1 t.val front (fun _ : Fin n=>4) tube target
      precision breadthCap lowOrder accuracy ho highCap lowCap lens test menu go board
      (fun a _=>near a)).2 t (by rfl)

end YM.Integration.WilsonAddressedPublicFirstCalendar
end
