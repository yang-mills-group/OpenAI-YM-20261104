import YM.Integration.WilsonReceivedCloseFoldedThermometer
import YM.Integration.WilsonReceivedCloseElectedProgram

/-! The original positioned 6/4/4 at its two actual physical meshes, with one
before-period election and all proper ordinary moments of the named covered program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseFoldedStationProgram
open Pert.Asymptotics
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory Extra.Histories MergeProof.Accent
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators


open WilsonReceivedCloseThreeSlotSchool Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
    {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
    (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
    (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)
    {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
    {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (hire:∀d,MintClock.Employment D φ d (R.rolls.L d))
    (q span degree:ℕ) (H angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "κ" => WilsonReceivedCloseThreeSlotSchool.vacuum R q
local notation "Sch₀" => WilsonReceivedCloseThreeSlotSchool.school R q

/-- The cutoff course is posted before the period, field positions and oriented measured frame. -/
def Heard : Prop :=
  ∀ᶠ m:ℕ in Filter.atTop, ∀ i (hi:m ≤ i+1), PaceR.Close R degree cap m (i+1) →
    ∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (κ)+2 ≤ R.alloy.B.a.clock.J m)
      (lesson:Lesson (N:=i+2) R hk D Q π Γ hi),
      PlanV.Path D R.alloy Q (Burn.horizon (κ)) (i+2) m π Γ ∧
      ∀ per:ℕ, ∃Ψ:(j:ℕ)→RG.Rep G (R.family.side j per),
        Concourse R.alloy R.kit R.T π Γ m (i+2) per (κ) Ψ ∧
        Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)) ∧
        ∀ A:Group R.family 6, A.station.k=i → A.station.checked f F A.horizon → close R A →
          ∀o:Positions (Fin 3) (R.family.side (i+2) per),
            WilsonReceivedCloseFoldedThermometer.Receipt (m:=m) (i:=i) (per:=per) (k:=κ) (φ:=φ) R simple A
              hk D Q π Γ Ψ books hi (Sch₀) o
              (WilsonReceivedCloseThreeSlotSchool.opportunity R q i (hk.trans (R.alloy.B.a.fits.mono hi)))
              lesson ahead q (q+226) span H angleCap ε


include house hp ep in
theorem on_course
    (enrolled:WilsonReceivedCloseElectedProgram.Heard R simple D Q books ahead (f:=f) (F:=F) q span degree H angleCap cap (ε/2)) :
    Heard R simple D Q books ahead (f:=f) (F:=F) q span degree H angleCap cap ε := by
  have gates:=WilsonReceivedCloseFoldedOrdinary.scheduled (k:=κ) R D (φ:=φ) levels (Sch₀).order
    (Sch₀).horizon (Sch₀).pieces simple 3 37 q degree span (WilsonReceivedCloseReportedWallet.unit R)
    cap H angleCap ε (WilsonReceivedCloseReportedWallet.covers R) hp ep
  filter_upwards [enrolled,gates,R.alloy.B.a.fits.deep.eventually_ge_atTop (κ)] with m issued dates stage
  intro i hi closeDates
  obtain ⟨π,Γ,hk,lesson,path,periods⟩:=issued i hi closeDates
  refine ⟨π,Γ,hk,lesson,path,?_⟩
  intro per
  obtain ⟨Ψ,history,top,reports⟩:=periods per
  refine ⟨Ψ,history,top,?_⟩
  intro A dating checked near o
  exact WilsonReceivedCloseFoldedThermometer.original R simple A hk D Q π Γ Ψ history scroll books
    house.licence.employed hi (Sch₀) o (WilsonReceivedCloseThreeSlotSchool.opportunity R q i
      (hk.trans (R.alloy.B.a.fits.mono hi))) lesson ahead q (q+226) span degree H angleCap cap ε hp ep
    house.licence.edges stage closeDates dates (reports A dating checked near o)

include house fund slow protection hp cp ep income hire in
theorem original : Heard R simple D Q books ahead (f:=f) (F:=F) q span degree H angleCap cap ε := by
  apply on_course R simple D Q scroll books ahead house q span degree H angleCap cap ε hp ep
  exact WilsonReceivedCloseElectedProgram.original R simple D Q scroll books ahead house (f:=f) (F:=F)
    fund slow protection income hire q span degree H angleCap cap (ε/2) hp cp (half_pos ep)

end YM.Integration.WilsonReceivedCloseFoldedStationProgram
