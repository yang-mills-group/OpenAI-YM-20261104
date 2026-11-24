import YM.Integration.WilsonReceivedCloseFoldedThermometer

/-! The independently registered three-source trajectory on any specified original
filed post, through each connected grade and the truncated ordinary partition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedClosePositionedReturn
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

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i+1)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

open FVA1Physical.TwoReset Laurent Stationary Comparison.RG02 Order
open WilsonCoveredOrdinaryPolynomial
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "J₀" => Stock.census (Fin 3)
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o
local notation "initial" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks
  S₀ levels school.order school.horizon school.pieces (i+1) hi (head)
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "return₃" x:max => WilsonOriginalCoveredEvolution.run (N:=i+2) R (Nat.lt_succ_self (i+1))
  π Γ (Burn.horizon k+2) school.order levels (WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x)

theorem ordinary {V : Type} [Fintype V] [DecidableEq V] {J : Marker.Census V}
    {d : ℕ} {K L : ℕ → Marker.Poly J} (given : ∀ i, i ≤ d → K i = L i) (g : ℂ) (s : J.Mode) :
    evaluated d K g s = evaluated d L g s := by
  unfold WilsonCoveredOrdinaryPolynomial.evaluated
  congr 1
  unfold WilsonCoveredOrdinaryPolynomial.ordinary
  refine Finset.sum_congr rfl fun h _ => Finset.prod_congr rfl fun t _ => ?_
  unfold WilsonCoveredOrdinaryPolynomial.row
  refine Finset.sum_congr rfl fun l hl => ?_
  dsimp only
  rw [given l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))]

theorem original (S:initial) (pupil:WilsonReceivedCloseCopiedThermometer.Published R simple A hk D Q π Γ Ψ books hi school o ahead S)
    {j:ℕ} (mj:m≤j)
    (Y:Wallet disks → Config G (R.family.side (j+1) per) → Poly J₀)
    (L:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels school.order school.horizon
      school.pieces j mj Y)
    (trail:WilsonReceivedCloseHistory.Trail (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels school.order
      school.horizon school.pieces hi (head) S j mj Y L) :
    ∃ ji : j ≤ (i+1), ∀ (x:Wallet disks) (field:Stationary.Link G (R.family.side j per)),
      let predicted := (fun d => (return₃ x) j ji (R.family.side j per) (dvd_refl _) d field)
      let student := Oak.student (i:=j) (n:=per) R hk D Q π Γ books mj L.op L.lesson ahead disks L.model school.order L.voter
      let writer := Air.craft student (fun t=>(student t).paint x) levels (π j) (tape₀)
      let K := fun d => Air.discharge writer d (Stationary.arm G (R.family.side j per) 1 field)
      (∀ d, d ≤ school.order → predicted d = K d) ∧
        ∀ (g:ℂ) (s:(J₀).Mode), evaluated school.order predicted g s = evaluated school.order K g s := by
  obtain ⟨ji,all⟩:=pupil j mj Y L trail
  refine ⟨ji,?_⟩
  intro x field predicted student writer K
  have paid:=Air.license student (fun v=>(student v).paint x) levels L.w L.issued.earning
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J j)) (fun v=>L.issued.earning.honor v x)
  have each (d:ℕ) (hd : d ≤ school.order) : predicted d = K d := by
    let n:=R.family.side j per
    have same:=WilsonOriginalCopiedMarkerLayout.same (dvd_refl n.val) student levels (π (j+1)) (π j) tape₀ x d field paid
    exact (all x n (dvd_refl _) d hd field).trans (same.trans (WilsonOriginalSelfPeriod.original student levels (π j) tape₀ x d field paid))
  exact ⟨each, ordinary each⟩

end YM.Integration.WilsonReceivedClosePositionedReturn
