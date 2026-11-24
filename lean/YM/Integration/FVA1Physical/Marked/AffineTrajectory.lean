import YM.Integration.FVA1Physical.Marked.AffinePrice

/-! The affine-null pre-reset estimate, actual mixed-mask budget and repeated
marked readings can be purchased on one trajectory, with any additional
obtainable schedule condition. The trajectory precedes the orders and
physical sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual.Season.Exchequer
open Filter Lattice RG Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open Push AnalyticBridge ConnectedActivityE6 VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open AllOrder Transit Transit.WheelP Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Quipu.Eluder Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
open Program Program.Certificate Booth BoothRent Calendars Moonset Rooms Studio
open Squall Parabola Emissions Integration LocalComparison FVA1Physical.Marked Prefect
open scoped BigOperators Classical Topology

theorem purchased_affine_marked {G : Gauge} (η ζ slope : ℕ → ℝ) (H : ℕ → ℕ)
    (g : G.Simple) (d : ℝ) (hd : 0 < d) (hη : ∀ i, 0 < η i) (hζ : ∀ i, 0 < ζ i)
    (hsmall : ∀ i, ζ i ≤ 1/4) (hdecay : Tendsto ζ atTop (𝓝 0)) (hlarge : Tendsto H atTop atTop)
    (positive : ∀ i, 0 < slope i) {goal : Schedule.Goal G} (extra : Schedule.Obtainable goal) :
    ∃ (X : Run G) (R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel)
      (Q : R.Tab X.rolls), X.family.path.levels.clock.kernel.penalty = d ∧ goal _ _ _ X.kit ∧
      TicketP X.alloy X.kit R Q ∧ AffineSteps X slope ∧
      ∀ (k n qd e length : ℕ) (B : Census (Fin n)) (ξ : Fin n → ℕ) (δ : ℝ),
        0 < n → qd ≤ Burn.horizon k + 1 → δ ≤ qd + 1 → 0 < δ →
        ∀ᶠ i in atTop, ∀ᶠ z in atTop, ∀ [Nonempty (Fin n)] (N : ℕ), z ≤ N →
          TestedSchedule X R ζ H B ξ i i k qd N z e length δ := by
  let program := Schedule.tandem (Prefect.Course (G := G) η H ζ) (Spending (fun i => 2*ζ i))
  have finance : Schedule.Obtainable (G := G) (Schedule.berth program) :=
    Schedule.all_chances g _ (Schedule.Prospecting.twin (Prefect.contracts η H ζ hη hζ hsmall)
      (Moonset.invoices _ (fun i => mul_pos zero_lt_two (hζ i))))
  obtain ⟨X,penalty,⟨distribution,uplink⟩,more,affine⟩ := Run.rampK g
    ((finance.also Calendars.Uplink.preferred).also (extra.also (obtain_affine g slope positive))) d hd
  obtain ⟨R,Q,ticket,profile,plateau,station⟩ := distribution
  have account := (show Prefect.Plateau _ _ _ _ _ _ _ from plateau).parent
  let grant : Grant X R Q η ζ H := ⟨⟨ticket,profile,account⟩,plateau,uplink⟩
  have woken (k z N : ℕ) (hc : Burn.horizon k + 2 ≤ X.alloy.B.a.clock.J z) (hz : z ≤ N) :
      Woken X R Q η ζ H grant.authority.resource k z N :=
    BoothRent.breaking X R Q η ζ H g ticket grant hc hz
  refine ⟨X,R,Q,penalty,more,ticket,affine_steps X g affine,?_⟩
  intro k n qd e length B ξ δ hn hqd horder hδ
  filter_upwards [enough (Fin n) B ξ qd] with i hi
  have schedules := Exchequer.pledged X R Q η ζ H g ticket i i station (woken k) δ hlarge hdecay B ξ e
    hn (le_refl n) hqd horder hδ le_rfl hi.1 hi.2
  filter_upwards [schedules,Hull.always_close (A := X.alloy) g length] with z ready close
  intro _ N hz
  exact (ready.2 N hz).tested ready.1 close

end YM.Qlocal.Actual.Season.Exchequer
