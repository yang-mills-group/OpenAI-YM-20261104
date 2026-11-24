import YM.Integration.FVA1Physical.Wilson.BarePrice
import YM.Integration.FVA1Physical.Marked.Purchased

/-! A single selected physical run supplies both the independently computed
normalized Wilson polynomial at the bare step and the marked represented
estimates in the purchased finite windows. The bare bound is for physical
readings. Identifying the outgoing represented error with that polynomial
below the bare step is a separate analytic obligation. -/

set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual.Season.Exchequer

open Filter Lattice RG Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open Push AnalyticBridge
open ConnectedActivityE6 VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open AllOrder Transit Transit.WheelP Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Quipu.Eluder Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
open Program Program.Certificate Booth BoothRent Calendars Moonset Rooms Studio
open Squall Parabola Emissions Integration LocalComparison
open YM.Wilson YM.Precision YM.FormalOPE.RG10.InversionTop
open YM.FVA2.CityHistory
open YM.PertExtension.Series YM.PertExtension.Series.Tested
open scoped Classical Topology

/-- All finite physically placed stencil censuses have a uniformly priced
normalized bare expansion on the chain of this particular run. -/
def BareWilsonPrices {G : Gauge} (A : Run G) : Prop :=
  ∀ (m d n : ℕ) (R : Census (Fin n))
    (V : Fin n → Stamp.Reservation A.family (A.family.side (m+1) 0) d)
    (q : ℝ), 0 < q → ∀ r : ℕ,
      ∃ δ B, 0 < δ ∧ 0 ≤ B ∧ ∀ (s : R.Mode) (p : ℕ)
        (y : Fin n → Site (A.family.side (m+1) p)),
        let S := A.family.path.levels.clock.op m p
        ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m p)),
          Bid.Larger (G := G) S → (∀ i, ‖u i‖ ≤ q) → ∀ g, 0 < g → g ≤ δ →
            let x := axesP G (A.family.side m p) u
            let D := MSMatch.SourceTop.datum R m p (FVA1Physical.Wilson.placeStencils V y) F t x
            ‖(MSMatch.SourceTop.torusVacuum m p x g)⁻¹ •
                MSMatch.SourceTop.torusFull m p (FVA1Physical.Wilson.placeStencils V y) x s.val g -
              peval (fun k => D.ordinaryCoefficient (RunFormalChain.fromRun A) r k s) r g‖ ≤
                B * g ^ (r+1)

/-- Choose the physical run once, before either the Wilson expansion order or
the represented-window data. Both conclusions retain that same witness. -/
theorem purchased_with_bare_wilson {G : Gauge}
    (η ζ : ℕ → ℝ) (H Lh : ℕ → ℕ) (g : G.Simple)
    (d : ℝ) (hd : 0 < d) (hη : ∀ i, 0 < η i) (hζ : ∀ i, 0 < ζ i)
    (hsmall : ∀ i, ζ i ≤ 1/4) (hdecay : Tendsto ζ atTop (𝓝 0))
    (hlarge : Tendsto H atTop atTop) :
    ∃ (X : Run G) (R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel),
      X.family.path.levels.clock.kernel.penalty = d ∧ BareWilsonPrices X ∧
      ∀ (k n qd e length : ℕ) (B : Marker.Census (Fin n)) (ξ : Fin n → ℕ) (δ : ℝ),
        0 < n → qd ≤ Burn.horizon k + 1 → δ ≤ qd + 1 → 0 < δ →
        ∀ᶠ i in atTop, ∀ᶠ z in atTop, ∀ [Nonempty (Fin n)] (N : ℕ), z ≤ N →
          TestedSchedule X R ζ H B ξ i i k qd N z e length δ := by
  obtain ⟨X, R, penalty, steps⟩ := purchased_readings η ζ H Lh g d hd hη hζ hsmall hdecay hlarge
  refine ⟨X, R, penalty, ?_, steps⟩
  intro m d' n C V q hq r
  exact FVA1Physical.Wilson.run_uniform C X V q hq r

end YM.Qlocal.Actual.Season.Exchequer
