import YM.Integration.WilsonThermometerPositionFirstReturn
import YM.Integration.WilsonThermometerNumericalStation
import YM.Integration.WilsonOriginalThermometerReportedPost

/-! The seven signed position filings of the enrolled three-field thermometer
enter the next Wilson block on their actual quiet layout and measured reset. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerPositionReceived
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonPositionThermometerCapStation WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity WilsonOriginalCopiedHistory
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (A:Group R.family 6) {m per k i:ℕ}
    (school:Syl.School k) (o:Positions (Fin 3) (R.family.side (i+2) per)) (x:Wallet disks)

def submitted :=
  WilsonThermometerPositionFirstReturn.submitted R (i+1) per levels o.origin
    (Pert.Asymptotics.regulatorRun R.family (i+2) per (i+2))
    (R.family.path.rep (i+2) per (i+2)).p.threshold (coordinates R A (i+2) (i+2) per)
    probe x school.order

variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (φ:ℕ→ℕ)
    (archive:Extension.UV.Archive R.alloy.B)
    (book:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
    (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (hi:m ≤ i+1)
    (simple:G.Simple) {δ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
    {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy}
    (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
    (shape:3 ≤ op.count) (space:14 ≤ school.horizon) (room:maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))

include Q Γ archive book hk hi fund slow late date checked near shape space room stage ranks in
theorem original :
    WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x =
      submitted R A school o x := by
  have heard := (eventually_atTop.mp (WilsonOriginalThermometerReportedGrading.original R (f:=f) (H:=F)
    simple fund slow 1 zero_lt_one)).choose_spec i late A date checked near 1 1 le_rfl per o.origin
    school.order op.count school.horizon op.stage k (R.alloy.B.a.clock.J (i+1)) shape space room
    stage (school.price.trans ((Nat.le_succ _).trans (hk.trans (R.alloy.B.a.fits.mono hi)))) ranks school.tall
  rw [WilsonThermometerNumericalStation.original R A D π (φ:=φ) school o x]
  exact WilsonThermometerPositionFirstReturn.original R (i+1) per levels o.origin
    (Pert.Asymptotics.regulatorRun R.family (i+2) per (i+2))
    (R.family.path.rep (i+2) per (i+2)).p.threshold (coordinates R A (i+2) (i+2) per)
    probe x school.order D Q π Γ book archive (hi.trans (Nat.le_succ _)) 1
    WilsonOriginalThermometerGradedPalette.positive _ heard.1 zero_lt_one
    (R.family.path.rep (i+2) per (i+2)).p (school.price.trans (Nat.le_succ _))

include Q archive book hk hi fund slow late date checked near shape space room stage ranks in
theorem returned (zero:Γ (i+1) 0=0) :
    WilsonOriginalCoveredEvolution.run R (Nat.lt_succ_self (i+1)) π Γ (Burn.horizon k+2) school.order
      levels (WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x) i (Nat.le_succ _) =
    block R (per:=per) (Nat.lt_trans (Nat.lt_succ_self i) (Nat.lt_succ_self (i+1))) school.order
      (receive (submitted R A school o x) (π (i+1)) (tape (Burn.horizon k+2)) levels (Γ (i+1)) zero
        (Burn.horizon k+2) school.order) := by
  rw [WilsonOriginalCoveredEvolution.actual R (Nat.lt_succ_self (i+1)) π Γ (Burn.horizon k+2)
    school.order levels _ i (Nat.lt_succ_self i) zero, WilsonOriginalCoveredEvolution.head,
    original R A school o x D Q π Γ φ archive book hk hi simple fund slow late date checked near
      op shape space room stage ranks]

end YM.Integration.WilsonThermometerPositionReceived
