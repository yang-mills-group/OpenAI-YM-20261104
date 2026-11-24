import YM.Integration.WilsonMovingMentorHistory
import YM.AllOrder.Burn.Notes

/-! All the successive physical cards and their identified Wilson corrections before the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorItinerary
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

abbrev CardAt {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
    (r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (k i : ℕ) :=
  PlanV.Card R.rolls r (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
    (R.alloy.B.a.clock.adm (i+1)) (Burn.horizon k)

theorem original {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} (plan : PlanV.Spec r Q R.alloy R.kit)
    {k m N : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
    (path : PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ) :
    ∃ (cards : (t : Set.Ico m N) → CardAt R r k t)
      (price : ∀ t : Set.Ico m N, Burn.horizon k+2 ≤ R.alloy.B.a.clock.J t),
      ∀ t : Set.Ico m N, let C := cards t
        PlanV.Journey r R.alloy (m:=t) (N:=N) C ∧ π (t+1)=C.extra ∧
        π t=(PlanV.litP r R.alloy Q (price t) C).laid C ∧
        Γ t=(PlanV.litP r R.alloy Q (price t) C).issue C ∧
        ∀ z ∈ Age.scope (Burn.horizon k+2), z.r=2 →
          |Γ t z.e| ≤ PlanV.capprice R.alloy (Burn.horizon k) t z := by
  classical
  have entrance (t : Set.Ico m N) := path.2.2 t t.property.1 t.property.2
  choose cards price walks using entrance
  refine ⟨cards,price,?_⟩
  intro t
  obtain ⟨journey,upper,lower,correction⟩ := walks t
  refine ⟨journey,upper,lower,correction,?_⟩
  rw [correction]
  exact (PlanV.readable r R.alloy R.kit Q plan (cards t) (price t) journey).2

end YM.Integration.WilsonMovingMentorItinerary
end
