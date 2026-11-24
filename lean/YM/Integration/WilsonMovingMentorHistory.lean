import YM.Integration.WilsonMovingMentorSpecRun
import YM.Integration.WilsonMovingMentorLodgeCalendar

/-! The physical hierarchy has one covariance table for every admitted rank.
Its original finite-cutoff history starts at the Wilson energy on every torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorHistory
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

theorem original {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G) (filed : WilsonMovingMentorSpec.Filed R.kit) :
    ∃ (r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : r.Tab R.rolls),
      PlanV.Spec r Q R.alloy R.kit ∧ ∀ (N n k : ℕ), n ≤ N → k+2 ≤ R.alloy.B.a.clock.J n →
        ∃ fields issue, PlanV.Path r R.alloy Q k N n fields issue ∧
          (∀ (s : Side) (d : ℕ), d ≤ k+2 →
            Pace.grouping 0 (fields N) (Age.scope (k+2)) (R.alloy.B.a.params N).clip (R.alloy.B.kin.path N N) d s =
              jet (Wilson.energy ∘ Stationary.input G s) (d+2)) ∧
          ∀ m, n ≤ m → m < N → ∀ z ∈ Age.scope (k+2), z.r = 2 →
            |issue m z.e| ≤ PlanV.capprice R.alloy k m z := by
  obtain ⟨r,Q,plan⟩ := filed
  refine ⟨r,Q,plan,?_⟩
  intro N n k cutoff rank
  obtain ⟨field,issue,path⟩ := PlanV.began r R.alloy R.kit Q plan N n cutoff rank
  refine ⟨field,issue,path,fun s d h => PlanV.started r R.alloy R.kit Q plan field issue path s h,?_⟩
  intro m atDate live z member twice
  obtain ⟨card,cost,walk,_,_,counter⟩ := path.2.2 m atDate live
  rw [counter]
  exact (PlanV.readable r R.alloy R.kit Q plan card cost walk).2 z member twice

/-- An incoming chart with the original component prices can be submitted
directly. The selected card carries that exact layout at the upper scale. -/
theorem received {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (Q : r.Tab R.rolls) (plan : PlanV.Spec r Q R.alloy R.kit)
    (N m k : ℕ) (live : m < N) (rank : k+2 ≤ R.alloy.B.a.clock.J m)
    (S : Layout G) (stock : PlanV.StateF r R.alloy k (m+1) S) :
    ∃ card : PlanV.Card R.rolls r (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m)
        (R.alloy.B.a.clock.adm (m+1)) k,
      PlanV.Journey r R.alloy (m:=m) (N:=N) card ∧ card.extra = S ∧
      PlanV.StateF r R.alloy k m ((PlanV.litP r R.alloy Q rank card).laid card) ∧
      ∀ z ∈ Age.scope (k+2), z.r = 2 →
        |(PlanV.litP r R.alloy Q rank card).issue card z.e| ≤ PlanV.capprice R.alloy k m z := by
  obtain ⟨card,journey,same⟩ := PlanV.fromst r R.alloy R.kit live Q plan S stock rank
  exact ⟨card,journey,same,PlanV.readable r R.alloy R.kit Q plan card rank journey⟩

/-- On this same issued table, all dated analytic charges fit any assigned
order of the measured coupling at the initial retained date. -/
theorem calendar {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G) (simple : G.Simple) (filed : WilsonMovingMentorSpec.Filed R.kit)
    (q : ℕ) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ start : ℕ in Filter.atTop, ∀ (N per : ℕ) (dates : Finset ℕ),
      (∀ n ∈ dates, start ≤ n ∧ n < N) →
      ∑ m ∈ dates, WilsonMovingMentorLodgePrice.amount R N per m ≤ ε*(Pert.Asymptotics.regulatorRun R.family N per start)^q := by
  obtain ⟨r,Q,plan⟩ := filed
  exact WilsonMovingMentorLodgeCalendar.total R simple Shop.edgeW plan.ladder q positive

end YM.Integration.WilsonMovingMentorHistory
end
