import YM.Integration.FVA1Physical.Marked.InheritedLong
import YM.Integration.FVA1Physical.Marked.HostPrice

/-! The failed short contribution of an inherited wallet, with a common
majorant selected before all independent tests. The true vacuum allowance
comes from the same physical trajectory at the same level. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Pressure Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset Finset
open scoped Classical BigOperators
variable {V Ω : Type} [Fintype V] [DecidableEq V] {B : Census V} {G : Gauge}
    {ξ : V → ℕ} {qd b : ℕ} {c : Side} {o : V → Site c} {P : Rep G c}

/-- Discard all masks and sum the available finite-order value envelopes.
This charge depends only on the order, source grading and physical coupling. -/
def valueInvoice (G : Gauge) (ξ : V → ℕ) (qd b : ℕ) (s : Senses B) (g : ℝ) : ℝ :=
  ∑ e : Fin (qd+1), ∑ n : Fin (e.val+Lagger.dues ξ s.val+1),
    |g^(e.val+Lagger.dues ξ s.val-n.val) / g^(Lagger.dues ξ s.val)| * Vase.ticketC G b n.val

omit [Fintype V] in
theorem wake_bound (A : Tale B G) (s : Senses B) (choose : A.Decision)
    {width : ℝ} (hA : A.Allows width 1) (hw : 0 < width) (g : ℝ) (U : Config G c) :
    |A.wake s choose o g U| ≤ valueInvoice G A.power A.depth A.method s g := by
  unfold Tale.wake valueInvoice
  simp only [Finset.sum_apply]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro e _
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro n _
  change |(g^A.stampE s e n / g^A.boom s) * (Tale.playing A choose o s e n U)| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold Tale.playing Album.picture
  simpa only [Real.norm_eq_abs, mul_one] using
    (Album.cap (fun k => choose s e n k ∧ (A.array s e n k).stage.Hears o)
      (A.array s e n) (o (Sonnet.root s)) U (hA.pay s e n) hw A.method)

def shortValue (W : Rooms.Wallet Ω o P B ξ qd b) (s : Senses B) (cut : ℕ) (g : ℝ)
    (u : Ω) (field : Config G c) : ℝ :=
  let A := Stanza.son (W.prediction u) b
  W.weight u s * A.wake s (A.short (W.activation u) cut) o g field

def ShortOwnersAt (W : Rooms.Wallet Ω o P B ξ qd b) (price : Parabola.Ray B)
    (β g κ : ℝ) : Prop :=
  ∀ s : Senses B,
    let S := Tale.court P.p.B (o (Sonnet.root s))
    let F := shortValue W s (Stores.till β) g
    let C := (price s.val)⁻¹ * valueInvoice G ξ qd b s g
    (∀ u rows U, P.activities.gasOccurrence P.p rows U * maskFailure P.p S (F u) U =
      if P.activities.admissible P.p U rows then
        ∑ i ∈ rows, (flagShare P S i U * P.activities.K i U * F u U) *
          ∏ j ∈ rows.erase i, P.activities.K j U else 0) ∧
    ∃ majorant : ℕ → ℝ, (∀ i, 0 ≤ majorant i) ∧
      (∀ u i U, |flagShare P S i U * P.activities.K i U * F u U| ≤ majorant i) ∧
      SumBudget (fun i => P.p.mass (S ∪ (P.activities.forced i).support) (majorant i))
        ((C*Real.exp (P.p.supportExponent*coverNumber P.p.B S))*((S.card : ℝ)*κ))

omit [Fintype V] in
theorem usable_short_owners (W : Rooms.Wallet Ω o P B ξ qd b) {O : V → Support c}
    {price : Parabola.Ray B} {width β allowance κ : ℝ} (hw : W.Usable O price width β allowance)
    (hp : 0 < width) (hK : P.activities.KBound P.p κ) (g : ℝ) :
    ShortOwnersAt W price β g κ := by
  intro s
  have charge : 0 ≤ valueInvoice G ξ qd b s g :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..)))
  refine ⟨fun u rows U => failed_occurrence P _ _ rows U, ?_⟩
  apply failed_source_budget P _ _ (mul_nonneg (inv_nonneg.mpr (hw.rental.pos _).le) charge) _ hK
  intro u U
  let A := Stanza.son (W.prediction u) b
  have weight : |W.weight u s| ≤ (price s.val)⁻¹ := by
    calc
      _ ≤ (price s.val)⁻¹ * 1 := (le_inv_mul_iff₀ (hw.rental.pos _)).mpr (hw.starts u s)
      _ = _ := mul_one _
  unfold shortValue
  rw [abs_mul]
  exact mul_le_mul weight (wake_bound A s _ (hw.optics u) hp g U) (abs_nonneg _)
    (inv_nonneg.mpr (hw.rental.pos _).le)

end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Exchequer
open Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder Transit Transit.WheelP
open Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Program Program.Certificate Calendars Moonset Rooms Studio Squall Parabola
open Emissions Integration LocalComparison FVA1Physical.Marked
open scoped BigOperators Classical

/-- Use the vacuum budget already paid on each admitted step, including later
resets. No external source bound or vacuum estimate is an additional input. -/
theorem purchased_short_owners {V Ω : Type} [Fintype V] [DecidableEq V] {G : Gauge}
    {X : Run G} {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
    {B : Census V} {ξ : V → ℕ} {b i k qd N z j p m : ℕ} {δ : ℝ}
    {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (t : ℕ) → RG.Rep G (X.alloy.B.a.S.side t p)}
    {o : (t : ℕ) → V → Site (X.family.side t p)} {S : (t : ℕ) → V → Support (X.family.side t p)}
    {price : Ray B} {W : Rooms.Wallet Ω (o m) (x m) B ξ qd b}
    (track : Metre X.alloy X.kit X.T path Γ z N p k x) (lo : z ≤ m) (hi : m ≤ N)
    (shell : Studio.Shell X R ξ b i price o S δ m W (x := x) (j := j) (k := k)) :
    ShortOwnersAt W (Studio.tagScale B X m j price) (X.alloy.B.a.clock.hatBeta m)
      (Coat.gStep (X.T.history N p m).beta) (Hull.divisor X.alloy.B.a m * Hull.divisor X.alloy.B.a m) := by
  rw [← (Hull.luminous X.alloy.B.a m).2.2]
  exact usable_short_owners W shell (Prior.yard_p ..) (track.1.walk m lo hi).truep.valid.labels.boundK _

end YM.Qlocal.Actual.Season.Exchequer
