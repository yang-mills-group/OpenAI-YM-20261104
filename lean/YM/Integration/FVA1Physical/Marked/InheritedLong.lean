import YM.Integration.FVA1Physical.Marked.PhysicalTests
import YM.Integration.FVA1Physical.Marked.AddressedTests
import YM.Integration.FVA1Physical.Marked.WalletSplit

/-! Apply the full-stencil identity, derivative charges and failed-mask
charges to the same purchased wallet after each reset. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Pressure Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset
open scoped Classical BigOperators
variable {V Ω : Type} [Fintype V] [DecidableEq V] {B : Census V} {G : Gauge}
    {ξ : V → ℕ} {qd b : ℕ} {c : Side} {o : V → Site c} {P : Rep G c}

/-- The long-row representation on an inherited wallet at its own cutoff
and physical coupling. The positive width is split between derivatives,
support geometry and the tail. -/
def LongStencilAt (W : Rooms.Wallet Ω o P B ξ qd b) (width β g : ℝ) : Prop :=
  let w := Stores.till β
  let v := width/3
  let t := v*P.p.B
  ∀ (u : Ω) (s : Senses B),
    let A := Stanza.son (W.prediction u) b
    let S := o (Sonnet.root s)
    let C₀ := Tale.court P.p.B S
    let choose := W.activation u
    (∀ field : Config G c,
      ((W.weight u s * A.wake s choose o g field : ℝ) : ℂ) =
        (W.render w g u field).part s.val +
          ((W.weight u s * (maskFailure P.p C₀ (A.wake s (A.short choose w) o g) field +
            A.wake s (A.long choose w) o g field) : ℝ) : ℂ)) ∧
    ∀ (e : Fin (A.depth+1)) (n : Fin (e.val+A.boom s+1)) (l : Lattice.Order)
      (f : ℕ → Set.Icc (-1 : ℝ) 1),
      let book := A.array s e n
      let keep := fun j => choose s e n j ∧ (book j).stage.Hears o
      let K := 1+(essence s).card+n.val
      (∀ j, PayR P.p ((book j).cone l S) (|(f j : ℝ)| * (book j).Sus P.p b 0)
        ((f j : ℝ) • (book j).read S b)) ∧
      SumBudget (fun j => if keep j ∧ w < (book j).momentum then
        |(f j : ℝ)| * ((book j).Sus P.p b 0 * Real.exp (t * coverNumber P.p.B ((book j).cone l S)))
        else 0)
        (P.p.threshold^n.val * Vase.humid G P.p.power P.p.order n.val b 0 K t v *
          Real.exp (-(v*(w+1 : ℕ)))) ∧
      ∀ field : Config G c,
        SumBudget (fun j => if keep j ∧ w < (book j).momentum ∧
          ¬Healthy P.p.threshold ((book j).cone l S) field then
          |(f j : ℝ)| * (|(book j).read S b field| * Real.exp (t*coverNumber P.p.B ((book j).cone l S)))
          else 0)
          (Vase.ticketC G b n.val * Real.exp (t*K) * Real.exp (-(v*(w+1 : ℕ))))

theorem usable_long_stencil (W : Rooms.Wallet Ω o P B ξ qd b) {O : V → Support c}
    {price : Parabola.Ray B} {width β allowance : ℝ}
    (hw : W.Usable O price width β allowance) (hp : 0 < width) (g : ℝ) :
    LongStencilAt W width β g := by
  intro u s
  constructor
  · intro field
    exact wallet_full_coefficient W u s (Stores.till β) g field hp (hw.optics u)
  · intro e n l f
    let a := width/3
    let t := a*P.p.B
    have ha : 0 < a := div_pos hp (by norm_num)
    have hden : (P.p.B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr P.p.B_pos.ne'
    have hd : t/P.p.B ≤ a := by simp [t,hden]
    let A := Stanza.son (W.prediction u) b
    let book := A.array s e n
    let keep := fun j => W.activation u s e n j ∧ (book j).stage.Hears o
    have h : book.Health (a+a+a) 1 := by
      rw [show a+a+a=width by dsimp [a]; ring]
      exact (hw.optics u).pay s e n
    obtain ⟨rows, total⟩ := long_regular_rows book l (o (Sonnet.root s)) P.p b
      (Stores.till β) f keep h ha (mul_nonneg ha.le (Nat.cast_nonneg _)) ha.le hd
    refine ⟨rows, ?_, ?_⟩
    · simp only [mul_one] at total
      convert total using 1
      funext j
      split <;> rfl
    · intro field
      have totalF := long_forced_rows book l (o (Sonnet.root s)) P.p b (Stores.till β) f keep h ha
        (mul_nonneg ha.le (Nat.cast_nonneg _)) ha.le hd field
      simp only [mul_one] at totalF
      convert totalF using 1
      funext j
      split <;> rfl
end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Exchequer
open Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder Transit Transit.WheelP
open Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Program Program.Certificate Calendars Moonset Rooms Studio Squall Parabola
open Emissions Integration LocalComparison FVA1Physical.Marked ComparisonDensity.Address
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {G : Gauge}
variable {X : Run G} {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
variable {ζ : ℕ → ℝ} {H : ℕ → ℕ} {B : Census V} {ξ : V → ℕ}
variable {b i k qd N z e length : ℕ} {δ : ℝ}

/-- The same physical trajectory carries all independent position test jets,
all admissions and the countable long-source correction at every reached
level, together with the complete existing paid short-model error. -/
theorem TestedSchedule.addressed_long (schedule : TestedSchedule X R ζ H B ξ b i k qd N z e length δ)
    (p j : ℕ) (hz : z ≤ j) (hN : j ≤ N) (hlen : j ≤ z+length) (D : V → Orbit)
    (addresses : RowAddresses D B ξ qd) (imag : V → Bool)
    (site : V → Site (X.family.side j p)) (supp : V → Support (X.family.side j p))
    (A : Stanza B G ξ qd) (mask : (Stanza.son A b).Decision) (amp : Senses B → ℝ)
    (w : V → ℝ) (cost : B.Mode → ℝ) (hcost : Spirit cost) (hw : ∀ v, 0 < w v)
    (hA : (Stanza.son A b).Allows (Prior.yard R (Burn.horizon k) i (X.alloy.B.a.clock.J j)) 1)
    (hsite : ∀ v, site v ∈ supp v)
    (hsupp : ∀ v, supp v ⊆ Uplink.habitat (X.family.side j p) (X.alloy.B.a.clock.hatBeta j) (site v))
    (hamp : ∀ s : Senses B, rent w cost s.val * |amp s| ≤ 1) :
    ∃ (path : ℕ → Floe.Layout G) (Γ : ℕ → Pace.Coin)
      (x : (m : ℕ) → RG.Rep G (X.alloy.B.a.S.side m p))
      (o : (m : ℕ) → V → Site (X.family.side m p)) (S : (m : ℕ) → V → Support (X.family.side m p))
      (U : (m : ℕ) → Rooms.Wallet (IndependentTests D) (o m) (x m) B ξ qd b),
      Metre X.alloy X.kit X.T path Γ z N p k x ∧ o j = site ∧ S j = supp ∧
      U j = Studio.herald X ξ b o S
        (fun f => testedStencil A (slotTests (fromAddressedTests D addresses imag f)))
        (fun _ => mask) (fun _ => amp) (x := x) j ∧
      Delivered X ζ H ξ b (rent w cost) o (Studio.speculum X δ qd z) U z (N := N) (j := j) (δ := δ) ∧
      (∀ m, z ≤ m → m ≤ j →
        Studio.Shell X R ξ b i (rent w cost) o S (Studio.speculum X δ qd z) m (U m)
          (x := x) (j := j) (k := k) ∧
        LongStencilAt (U m) (Prior.yard R (Burn.horizon k) i (X.alloy.B.a.clock.J m))
          (X.alloy.B.a.clock.hatBeta m) (Coat.gStep (X.T.history N p m).beta)) ∧
      ∀ m, z ≤ m → m < j → TestedAt (priceNormalized cost (U m).other) (x m).p w
        (Hull.divisor X.alloy.B.a m) ((Real.exp 1+1)*Studio.target δ qd (X.T.history N p z).beta)
        (Hull.divisor X.alloy.B.a m * (Coat.gStep (X.T.history N p (m+1)).beta)^e) := by
  letI : Nonempty (IndependentTests D) :=
    ⟨fun _ => ⟨0, Orbit.Bill.more Orbit.Bill.zero zero_le_one⟩⟩
  obtain ⟨path, Γ, periods⟩ := schedule
  obtain ⟨x, hx, opens⟩ := periods p
  obtain ⟨o, S, U, ho, hS, _, start, _, delivered, shells, paid⟩ := opens j hz hN hlen
    (IndependentTests D) site supp (fun f => testedStencil A (slotTests (fromAddressedTests D addresses imag f)))
    (fun _ => mask) (fun _ => amp) w cost hcost hw
    (fun f => addressed_stencil_allows D addresses imag f A hA) hsite hsupp (fun _ => hamp)
  refine ⟨path, Γ, x, o, S, U, hx, ho, hS, start, delivered, ?_, paid⟩
  intro m hm hj
  have hs := shells m hm hj
  exact ⟨hs, usable_long_stencil (U m) hs (Prior.yard_p ..) _⟩

end YM.Qlocal.Actual.Season.Exchequer
