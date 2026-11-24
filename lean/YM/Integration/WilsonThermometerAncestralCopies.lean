import YM.Integration.WilsonThermometerAncestralTrace
import YM.Integration.WilsonOriginalCoveredTrail
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralCopies
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

open OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace WilsonPositionThermometerGradedSource WilsonThermometerCourseHearing

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt

variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m ≤ t)
open WilsonOriginalCopiedHistory FVA1Physical.TwoReset
open WilsonReceivedFirstTrace
local notation "J₃" => Stock.census (Fin 3)
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teacher" j:max mj:max P:max => Oak.student (i:=j) (n:=per) R hk D tab π Γ books mj
  (P).op (P).lesson ahead WilsonThermometerCourseHearing.disks (P).model order (P).voter
local notation "store" P:max c:max cut:max => WilsonReceivedFirstTrace.install R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W P c cut

private theorem retest {i:ℕ} (mi: m ≤ i)
    {f g:Wallet WilsonThermometerCourseHearing.disks → Config G (R.family.side (i+1) per) → Poly J₃}
    (P:post i mi f) (L:post i mi g) (same:f=g) (h:HEq P L)
    (x:Wallet WilsonThermometerCourseHearing.disks) (grid:Side)
    (div:(R.family.side i per).val ∣ grid.val) (d:ℕ) (field:Stationary.Link G grid) :
    peek div (teacher i mi P) ages (π (i+1)) tape₀ x d field =
      peek div (teacher i mi L) ages (π (i+1)) tape₀ x d field :=by
  cases same
  cases eq_of_heq h
  rfl

/-- The signed earlier pupil of the actual reached physical library computes the original
    independent evolution of any entered, separately specified upper bank. -/
theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {i:ℕ} (mi: m ≤ i) (it:i ≤ t)
    (L:post i mi (faces (it.trans_lt top))) (q:ℕ) (ε:ℝ)
    (reached:WilsonThermometerAncestralTrace.Reached R simple A top o hk D tab π Γ Ψ books ahead
      order shelf seats W mt inlet counted q ε mi it L)
    (pass:Pass D tab R.alloy R.kit) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)
    (x:Wallet WilsonThermometerCourseHearing.disks)
    (upper:WilsonOriginalCopiedHistory.Values G (J₃) (R.family.side t per))
    (entered:∀(grid:Side)(div:(R.family.side t per).val ∣ grid.val)(d:ℕ),d ≤ order → ∀z,
      upper grid div d z=peek div (teacher t mt inlet) ages (π (t+1)) tape₀ x d z) :
    ∀(grid:Side)(div:(R.family.side i per).val ∣ grid.val)(d:ℕ),d ≤ order →
      ∀field:Stationary.Link G grid,
      (WilsonOriginalCoveredEvolution.run R top π Γ (Burn.horizon k+2) order ages upper) i it grid div d field=
        peek div (teacher i mi L) ages (π (i+1)) tape₀ x d field :=by
  obtain ⟨P,c,history,align,_inputs,_outputs⟩:=reached
  have run:=history.trail R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
    WilsonThermometerCourseHearing.sectors ages order shelf seats W mt (faces top) inlet counted top q ε
  obtain ⟨_,retained⟩:=WilsonOriginalCoveredTrail.full R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    mt (faces top) (store inlet counted top) x upper top W.course pass month fits W.narrow entered run
  intro grid div d hd field
  exact (retained grid div d hd field).trans
    (retest R hk D tab π Γ Ψ books ahead order shelf seats mi P L
      (WilsonThermometerAncestralTrace.same R simple A top o refs it) (HEq.symm align) x grid div d field)

end YM.Integration.WilsonThermometerAncestralCopies
