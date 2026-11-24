import YM.Integration.FVA1Physical.Marked.PaidLocal

/-! The physical finite-marker, divided forced budget on the bought trajectory. -/
set_option autoImplicit false
noncomputable section

namespace YM.Qlocal.Actual.Season.Exchequer
open Filter Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder Transit Transit.WheelP
open Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Program Program.Certificate Calendars Moonset Rooms Studio Squall Parabola
open Emissions Integration LocalComparison FVA1Physical.Marked Finset Push.AbsoluteSums
open scoped BigOperators Classical Topology

/-- On the actual common paid trajectory, finite marker degree suffices for
arbitrary coupling order in the *divided*, support-weighted failed-mask
component. All common test scales are restored and the constant contains
only the degree, observable orders, number of tags and gauge group. -/
theorem purchased_paid_forced {G : Gauge} (X : Run G) (gauge : G.Simple)
    {R₀ : Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel} {Q₀ : R₀.Tab X.rolls}
    (ticket : TicketP X.alloy X.kit R₀ Q₀) (q load : ℕ) :
    ∀ᶠ m in atTop, ∀ {V Ω M : Type} [Fintype V] [DecidableEq V] [Fintype M] [Nonempty M]
      {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
      {B : Census V} {ξ : V → ℕ} {b i k qd N z j p : ℕ} {δ : ℝ}
      {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
      {x : (t : ℕ) → RG.Rep G (X.alloy.B.a.S.side t p)}
      {o : (t : ℕ) → V → Site (X.family.side t p)} {S : (t : ℕ) → V → Support (X.family.side t p)}
      {T : Ray B} {W : Rooms.Wallet Ω (o m) (x m) B ξ qd b},
      Metre X.alloy X.kit X.T path Γ z N p k x → z ≤ m → m ≤ N →
      Studio.Shell X R ξ b i T o S δ m W (x := x) (j := j) (k := k) →
      ∀ modes : M → Senses B, 3 * Fintype.card M + ∑ s, Lagger.dues ξ (modes s).val ≤ load →
      let d := Hull.divisor X.alloy.B.a m
      let pos := fun s => o m (Sonnet.root (modes s))
      let src := fun s => Tale.court (x m).p.B (pos s)
      let g := Coat.gStep (X.T.history N p m).beta
      let ray := Studio.tagScale B X m j T
      let F := fun u s => shortValue W (modes s) (Stores.till (X.alloy.B.a.clock.hatBeta m)) g u
      ∃ bound : (s : M → M) → representatives s → ℕ → ℝ,
        (∀ s k i, 0 ≤ bound s k i) ∧
        (∀ u (π : M → ℕ) U, |∏ k : representatives (hostPattern π),
          ownerBlock (x m) (fibre π (distinctHosts π k)) src F u (distinctHosts π k) U| ≤
          ∏ k, bound (hostPattern π) k (distinctHosts π k)) ∧
        SumBudget (fun π : M → ℕ => (∏ s, ray (modes s).val) * (d⁻¹ * ∏ k : representatives (hostPattern π),
          (x m).p.mass (enlarged (x m) (fibre π (distinctHosts π k)) src (distinctHosts π k))
            (bound (hostPattern π) k (distinctHosts π k))))
          (((Fintype.card (M → M):ℝ)/2 * (∏ s, 2^(Lagger.dues ξ (modes s).val) *
             valueInvoice G ξ qd b (modes s) 1) * 2^q) * g^q) := by
  let A := X.alloy.B.a
  filter_upwards [purchased_all_host_assignments X gauge (q+load),
    schedule_support_credit X ticket, (Corrected.Grows.beta A gauge).eventually_ge_atTop 2] with m hard credit two
  intro V Ω M _ _ _ _ R B ξ b i k qd N z j p δ path Γ x o S T W track lo hi shell modes hload d pos src g ray F
  let y := A.clock.hatBeta m
  let t := (X.T.history N p m).beta
  let w := ∏ s, ray (modes s).val
  let price := ∏ s, Real.exp (x m).p.supportExponent * ((ray (modes s).val)⁻¹ * valueInvoice G ξ qd b (modes s) g)
  let invoice := ∏ s, 2^(Lagger.dues ξ (modes s).val) * valueInvoice G ξ qd b (modes s) 1
  let card : ℝ := Fintype.card (M → M)
  have hy : 1 ≤ y := by linarith
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hb := ((X.T.sticks N p).prices m (Nat.zero_le _) hi).2
  have hb0 : 0 < t := (half_pos hy0).trans_le hb.1
  have hb1 : 1 ≤ t := by linarith [hb.1, two]
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hb0)
  have hs : Real.sqrt t ≤ t := (Real.sqrt_le_left hb0.le).mpr (by nlinarith)
  have hs2 : 1/y ≤ 2*g := by
    change 1/y ≤ 2/(Real.sqrt t)
    exact (div_le_div_iff₀ hy0 (Real.sqrt_pos.mpr hb0)).mpr (by simpa only [one_mul] using hs.trans hb.2)
  have hpow : (y^q)⁻¹ ≤ 2^q * g^q := by simpa only [one_div, inv_pow, mul_pow] using pow_le_pow_left₀ (by positivity) hs2 q
  have hτ : Real.exp (x m).p.supportExponent ≤ y^3 := by rw [(track.1.walk m lo hi).truep.point]; exact credit
  have hw : 0 ≤ w := prod_nonneg (fun s _ => (shell.rental.pos _).le)
  have hk : 0 ≤ invoice := prod_nonneg (fun s _ => mul_nonneg (by positivity)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..)))
  have hc : 0 ≤ card/2 := by unfold card; positivity
  have hp : w*price ≤ invoice*y^load := (invoice_product G ξ qd b modes ray (fun s => shell.rental.pos _) two hb hτ).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hload) hk)
  obtain ⟨bound,h0,h1,h2⟩ := hard track lo hi shell modes
  refine ⟨bound,h0,h1,budget_loosen (budget_scale hw h2) ?_⟩
  change w * (card*price * (y^(q+load))⁻¹ / 2) ≤ card / 2 * invoice * 2^q * g^q
  calc
    _ = (card/2) * (w*price) * (y^(q+load))⁻¹ := by ring
    _ ≤ (card/2) * (invoice*y^load) * (y^(q+load))⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (by positivity)
    _ = (card/2)*invoice*(y^q)⁻¹ := by rw [pow_add]; field_simp
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hk)

end YM.Qlocal.Actual.Season.Exchequer
