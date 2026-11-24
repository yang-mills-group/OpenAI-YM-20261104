import YM.Integration.FVA1Physical.Marked.M7a

/-! The marked comparison on the purchased physical trajectory, initialized
with a real stencil and its actual density. Every regular and forced test is
applied to the wallet delivered along that same trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Qlocal.Actual.Season.Exchequer
open Filter Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open AllOrder Transit Transit.WheelP Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Quipu.Eluder Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
open Program Program.Certificate Booth BoothRent Calendars Moonset Rooms Studio
open Squall Parabola Emissions Integration LocalComparison FVA1Physical.Marked
open scoped BigOperators Classical Topology

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {G : Gauge}
variable (X : Run G) (R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel)
variable (ζ : ℕ → ℝ) (H : ℕ → ℕ) (B : Census V) (ξ : V → ℕ)
variable (b i k qd N z e length : ℕ) (δ : ℝ)

/-- One schedule and, for each physical period, one actual represented trajectory.
Every set of admissible real stencil inputs at the end of a finite window
has one transported wallet for all intermediate stages and all row tests. -/
def TestedSchedule : Prop :=
  ∃ (w : ℕ → Layout G) (Γ : ℕ → Pace.Coin), ∀ p : ℕ,
    ∃ x : (m : ℕ) → RG.Rep G (X.alloy.B.a.S.side m p),
      Metre X.alloy X.kit X.T w Γ z N p k x ∧
      ∀ (j : ℕ), z ≤ j → j ≤ N → j ≤ z + length →
        ∀ (Ω : Type) [Nonempty Ω] (site : V → Site (X.family.side j p))
          (supp : V → Support (X.family.side j p))
          (stanza : Ω → Stanza B G ξ qd) (choose : ∀ t, (Stanza.son (stanza t) b).Decision)
          (amplitude : Ω → Senses B → ℝ) (weights : V → ℝ) (cost : B.Mode → ℝ),
          Spirit cost → (∀ v, 0 < weights v) →
          (∀ t, (Stanza.son (stanza t) b).Allows
            (Prior.yard R (Burn.horizon k) i (X.alloy.B.a.clock.J j)) 1) →
          (∀ v, site v ∈ supp v) →
          (∀ v, supp v ⊆ Uplink.habitat (X.family.side j p)
            (X.alloy.B.a.clock.hatBeta j) (site v)) →
          (∀ t s, Emissions.rent weights cost (s : Senses B).val * |amplitude t s| ≤ 1) →
          ∃ (o : (m : ℕ) → V → Site (X.family.side m p))
            (S : (m : ℕ) → V → Support (X.family.side m p))
            (U : (m : ℕ) → Rooms.Wallet Ω (o m) (x m) B ξ qd b),
            o j = site ∧ S j = supp ∧ Studio.Pinned X o S z j ∧
            U j = Studio.herald X ξ b o S stanza choose amplitude (x := x) j ∧
            (∀ (t : Ω) (field : Config G (X.family.side j p)),
              Studio.interpretation (N := N) X ξ b j (U j) t field =
                Poly.pass ((U j).render (Stores.till (X.alloy.B.a.clock.hatBeta j))
                  (Coat.gStep (X.family.path.β N p j)) t field) *
                  Poly.bead B (((X.family.path.rep N p j).eval field) : ℂ)) ∧
            Delivered X ζ H ξ b (Emissions.rent weights cost) o (Studio.speculum X δ qd z)
              U z (N := N) (j := j) (δ := δ) ∧
            (∀ m, z ≤ m → m ≤ j →
              Studio.Shell X R ξ b i (Emissions.rent weights cost) o S (Studio.speculum X δ qd z)
                m (U m) (x := x) (j := j) (k := k)) ∧
            ∀ m, z ≤ m → m < j →
              TestedAt (priceNormalized cost (U m).other) (x m).p weights
                (Hull.divisor X.alloy.B.a m)
                ((Real.exp 1 + 1) * Studio.target δ qd (X.T.history N p z).beta)
                (Hull.divisor X.alloy.B.a m * (Coat.gStep (X.T.history N p (m + 1)).beta) ^ e)

variable {X R ζ H B ξ b i k qd N z e length δ}
variable {η : ℕ → ℝ} {Q : R.Tab X.rolls} {hK : TicketP X.alloy X.kit R Q} {r0 : ℕ}

theorem ScheduleOf.tested (schedule : ScheduleOf X R Q η ζ H hK ξ b i r0 k qd N z B δ)
    (fees : Fees X B ζ H z qd e δ) (close : ∀ j ≤ z + length, Hull.Close X.alloy.B.a z j) :
    TestedSchedule X R ζ H B ξ b i k qd N z e length δ := by
  obtain ⟨w, Γ, Θ, _, periods, calm⟩ := schedule.tickets
  refine ⟨w, Γ, ?_⟩
  intro p
  obtain ⟨x, hx⟩ := periods p
  refine ⟨x, hx, ?_⟩
  intro j hzj hjN hlen Ω _ site supp stanza choose amplitude weights cost hcost hweights
    hstanza hsite hsupp hamplitude
  obtain ⟨o, S, ho, hS, hpin⟩ := Studio.arrange_pos (X := X) site supp hzj
  obtain ⟨_, U, gallery, delivered, initial⟩ := Calm.provide
    (X := X) (R := R) (Q := Q) (η := η) (ζ := ζ) (H := H) (w := w) (Γ := Γ)
    (hK := hK) (ξ := ξ) (b := b) (i := i) (hp := hx) (T := Emissions.rent weights cost)
    (Xo := o) (Xs := S) (Θ := Θ) (δ := δ) (u' := Studio.speculum X δ qd z) (hCalm := calm)
    (hc := hzj) (he := hjN) (hT := Parabola.conventional_p hcost weights hweights)
    (Y0 := stanza) (Z := choose) (v0 := amplitude) (hY := hstanza)
    (hZ := by simpa only [ho, hS] using hsite)
    (hV := by simpa only [ho, hS] using hsupp) (h0 := hamplitude) (hO := hpin) (hα := fees.coat)
  refine ⟨o, S, U, ho, hS, hpin, gallery.paid, ?_, delivered, gallery.steady, ?_⟩
  · simpa only [gallery.paid] using initial
  · intro m hzm hmj
    exact Delivered.independent_readings X weights cost hcost hweights rfl hzm hmj rfl
      (close j hlen) fees delivered

/-- A physical run with the prescribed penalty is chosen before perturbative
orders, finite marker loads and periods. The admissible model height, wallet,
represented path, charged initial estimate and finite-window error bounds are
then constructed. Input marker supports need only be specified on the initial
mesh. They and all stencil inputs may be chosen after the UV onset. -/
theorem purchased_readings {G : Gauge} (η ζ : ℕ → ℝ) (H Lh : ℕ → ℕ) (g : G.Simple)
    (d : ℝ) (hd : 0 < d) (hη : ∀ i, 0 < η i) (hζ : ∀ i, 0 < ζ i)
    (hsmall : ∀ i, ζ i ≤ 1/4) (hdecay : Tendsto ζ atTop (𝓝 0))
    (hlarge : Tendsto H atTop atTop) :
    ∃ (X : Run G) (R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel),
      X.family.path.levels.clock.kernel.penalty = d ∧
      ∀ (k n qd e length : ℕ) (B : Marker.Census (Fin n)) (ξ : Fin n → ℕ) (δ : ℝ),
        0 < n → qd ≤ Burn.horizon k + 1 → δ ≤ qd + 1 → 0 < δ →
        ∀ᶠ i in atTop, ∀ᶠ z in atTop, ∀ [Nonempty (Fin n)] (N : ℕ), z ≤ N →
          TestedSchedule X R ζ H B ξ i i k qd N z e length δ := by
  obtain ⟨X, R, Q, grant, _, _, penalty, _, _, schedules⟩ :=
    purchased (η := η) (ζ := ζ) (H := H) (g := g) (Lh := Lh) d hd hη hζ hsmall hdecay hlarge
  refine ⟨X, R, penalty, ?_⟩
  intro k n qd e length B ξ δ hn hqd horder hδ
  filter_upwards [enough (Fin n) B ξ qd] with i hi
  filter_upwards [schedules k n n qd i i e B ξ δ hn le_rfl hqd horder hδ le_rfl hi.1 hi.2,
    Hull.always_close (A := X.alloy) g length] with z hready hclose
  intro _ N hzN
  exact (hready.2 N hzN).tested hready.1 hclose

end YM.Qlocal.Actual.Season.Exchequer
