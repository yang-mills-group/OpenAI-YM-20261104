import YM.Integration.FVA1Physical.Marked.Purchased
import YM.Integration.FVA1Physical.Marked.StencilTests

/-! Apply the purchased actual schedule to the full product of bounded signed
stencil tests, with a separate test at each occupied source and each term. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

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

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {G : Gauge}
variable {X : Run G} {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
variable {ζ : ℕ → ℝ} {H : ℕ → ℕ} {B : Census V} {ξ : V → ℕ}
variable {b i k qd N z e length : ℕ} {δ : ℝ}

local notation "Query" => V → StencilTests B ξ qd
local instance : Nonempty (Set.Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num, by norm_num⟩⟩

/-- Buy one represented physical trajectory and one wallet carrying every
independent signed source test. The initial stencil equality, its actual vacuum
factor and its full budget at every subsequent tested row refer to that wallet. -/
theorem TestedSchedule.slot_sources (schedule : TestedSchedule X R ζ H B ξ b i k qd N z e length δ)
    (p j : ℕ) (hz : z ≤ j) (hN : j ≤ N) (hlen : j ≤ z + length)
    (site : V → Site (X.family.side j p)) (supp : V → Support (X.family.side j p))
    (A : Stanza B G ξ qd) (mask : (Stanza.son A b).Decision) (amp : Senses B → ℝ)
    (w : V → ℝ) (cost : B.Mode → ℝ) (hcost : Spirit cost) (hw : ∀ v, 0 < w v)
    (hA : (Stanza.son A b).Allows (Prior.yard R (Burn.horizon k) i (X.alloy.B.a.clock.J j)) 1)
    (hsite : ∀ v, site v ∈ supp v)
    (hsupp : ∀ v, supp v ⊆ Uplink.habitat (X.family.side j p)
      (X.alloy.B.a.clock.hatBeta j) (site v))
    (hamp : ∀ s : Senses B, rent w cost s.val * |amp s| ≤ 1) :
    ∃ (path : ℕ → Floe.Layout G) (Γ : ℕ → Pace.Coin)
      (x : (m : ℕ) → RG.Rep G (X.alloy.B.a.S.side m p))
      (o : (m : ℕ) → V → Site (X.family.side m p))
      (S : (m : ℕ) → V → Support (X.family.side m p))
      (U : (m : ℕ) → Rooms.Wallet Query (o m) (x m) B ξ qd b),
      Metre X.alloy X.kit X.T path Γ z N p k x ∧ o j = site ∧ S j = supp ∧
      U j = Studio.herald X ξ b o S (fun t : Query => testedStencil A (slotTests t))
        (fun _ => mask) (fun _ => amp) (x := x) j ∧
      (∀ (t : Query) (f : Config G (X.family.side j p)),
        Studio.interpretation (N := N) X ξ b j (U j) t f =
          Poly.pass ((U j).render (Stores.till (X.alloy.B.a.clock.hatBeta j))
            (Coat.gStep (X.family.path.β N p j)) t f) *
            Poly.bead B (((X.family.path.rep N p j).eval f) : ℂ)) ∧
      Delivered X ζ H ξ b (rent w cost) o (Studio.speculum X δ qd z) U z
        (N := N) (j := j) (δ := δ) ∧
      (∀ m, z ≤ m → m ≤ j →
        Studio.Shell X R ξ b i (rent w cost) o S (Studio.speculum X δ qd z)
          m (U m) (x := x) (j := j) (k := k)) ∧
      ∀ m, z ≤ m → m < j →
        TestedAt (priceNormalized cost (U m).other) (x m).p w (Hull.divisor X.alloy.B.a m)
          ((Real.exp 1 + 1) * Studio.target δ qd (X.T.history N p z).beta)
          (Hull.divisor X.alloy.B.a m * (Coat.gStep (X.T.history N p (m + 1)).beta) ^ e) := by
  obtain ⟨path, Γ, periods⟩ := schedule
  obtain ⟨x, hx, opens⟩ := periods p
  obtain ⟨o, S, U, ho, hS, _, hu, hborn, hrun, hnext, htest⟩ := opens j hz hN hlen Query site supp
    (fun t => testedStencil A (slotTests t)) (fun _ => mask) (fun _ => amp) w cost hcost hw
    (fun t => testedStencil_allows A (slotTests t) hA) hsite hsupp (fun _ => hamp)
  exact ⟨path, Γ, x, o, S, U, hx, ho, hS, hu, hborn, hrun, hnext, htest⟩

end YM.Qlocal.Actual.Season.Exchequer
