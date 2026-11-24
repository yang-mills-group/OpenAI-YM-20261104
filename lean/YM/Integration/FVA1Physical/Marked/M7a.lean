import YM.Qlocal.Moonset.Titan
import YM.Qlocal.Moonset.Costed
import YM.Qlocal.Ageing
import YM.Qlocal.Dialect.Response
import YM.Integration.FVA1Physical.TestedBudget

/-! Independently tested regular, caption, and forced charges in each delivered
M7a wallet. The theorem reads precisely the presentation normalized by the
incoming mode envelopes and divides the forced sum by the actual divisor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked

open Lattice RG Wilson Marker RG3.Script.Picnic LocalComparison Push.AbsoluteSums
open scoped BigOperators Classical

/-- The complete tested readings of one presentation, with each forced row divided
by the stage allowance. The tests vary independently from one row to the next. -/
def TestedAt {G : Gauge} {n : Side} {V Ω : Type} [DecidableEq V] {B : Census V}
    {P : Rep G n} {o : V → Site n} (pres : Taste Ω o P B) (p : BudgetPoint)
    (w : V → ℝ) (κ regularPrice forcedPrice : ℝ) : Prop :=
  ∀ (v : V) (unitTest : Ω) (reg cap : ℕ → Ω) (force : ℕ × ℕ → Ω)
    (field : ℕ × ℕ → Config G n) (jet : ∀ i, DerivativeTest p (pres.menu.branch i) (o v) G),
    (∃ b c : ℝ,
      SumBudget (fun i => if v ∈ (pres.menu.rays i).val then Poly.toll w (pres.menu.rays i) *
        p.mass (pres.menu.branch i) ((jet i).read (pres.menu.regular (reg i) i)) else 0) b ∧
      SumBudget (fun i => if v ∈ (pres.tag i).val then Poly.toll w (pres.tag i) *
        p.mass (pres.site i) ‖pres.score (cap i) i‖ else 0) c ∧
      w v * ‖pres.menu.global unitTest v‖ + b + c ≤ regularPrice) ∧
    SumBudget (fun i : ℕ × ℕ => κ⁻¹ *
      (if v ∈ (pres.menu.marks i.1 i.2).val then Poly.toll w (pres.menu.marks i.1 i.2) *
        p.mass (P.activities.forced i.1).support ‖pres.menu.force (force i) i.1 i.2 (field i)‖ else 0)) forcedPrice

end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Studio
open Filter Lattice RG Wilson Tree Marker RG3.Script.Picnic Extra.Trajectories Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe Integration LocalComparison FVA1Physical
open ConnectedActivityE6 Program Program.Certificate Squall Parabola Emissions Moonset Rooms
open FVA1Physical.Marked
open scoped BigOperators Classical Topology

variable {V Ω : Type} [DecidableEq V] [Fintype V] [Nonempty V] [Nonempty Ω]
variable {B : Marker.Census V} {G : Gauge} (X : Run G) {m z j N p b qd e : ℕ} {δ : ℝ}
variable {x : (i : ℕ) → RG.Rep G (X.alloy.B.a.S.side i p)} {ξ : V → ℕ}
variable {ζ : ℕ → ℝ} {H : ℕ → ℕ} {T : Ray B} {D' : ℝ}
variable {Xo : (i : ℕ) → V → Site (X.family.side i p)}
variable {U : (i : ℕ) → Rooms.Wallet Ω (Xo i) (x i) B ξ qd b}
variable (w : V → ℝ) (cost : B.Mode → ℝ)
local notation "κₘ" => Hull.divisor X.alloy.B.a m
local notation "formalRegular" => (Real.exp 1 + 1) * Studio.target δ qd (X.T.history N p z).beta
local notation "formalForced" => κₘ * (Coat.gStep (X.T.history N p (m + 1)).beta) ^ e
local notation "pres" => priceNormalized cost (U m).other

/-- Spend the repeated, physically priced M7a allowance on independently chosen
label tests, including the full factorial regular readings and divided forced
readings. The input self-energy and all mode prices use the M7a conventions. -/
theorem Delivered.independent_readings (hcost : Spirit cost) (hw : ∀ i, 0 < w i)
    (hray : T = Emissions.rent w cost) (hz : z ≤ m) (hm : m < j)
    (hD : D' = Studio.speculum X δ qd z) (hclose : Hull.Close X.alloy.B.a z j)
    (hfees : Fees X B ζ H z qd e δ)
    (h : Delivered X ζ H ξ b T Xo D' U z (N := N) (j := j) (δ := δ))
    : TestedAt pres (x m).p w κₘ formalRegular formalForced := by
  obtain ⟨W⟩ := Delivered.heading (X := X) (v' := w) (C' := cost) (hΨ := hcost) (hw := hw)
    (hZ := hray) (ht := hz) (he := hm) (hp := hD) (hC := hclose) (hF := hfees) (h := h)
  intro v unitTest reg cap force field jet
  obtain ⟨hr, hf⟩ := tested_full_budget W.budget v unitTest reg cap force field jet
  refine ⟨hr, ?_⟩
  have hf' := budget_scale (inv_nonneg.mpr W.budget.divisor.le) hf
  simpa only [inv_mul_cancel_left₀ W.budget.divisor.ne'] using hf'

/-- For any fixed number of RG steps, both the physical close-window condition
and the marked fee estimates are automatic sufficiently far into the UV. The
threshold is chosen before the period, UV start, field, and test presentation. -/
theorem eventual_window_readings (hG : G.Simple) (length : ℕ) (hδ : 0 < δ)
    (horder : δ ≤ qd + 1) (hH : Tendsto H atTop atTop) (hζ : Tendsto ζ atTop (𝓝 0)) :
    ∀ᶠ z in atTop, ∀ (p N j m : ℕ), z ≤ m → m < j → j ≤ z + length →
      ∀ (x : (i : ℕ) → RG.Rep G (X.alloy.B.a.S.side i p)) (ξ : V → ℕ) (b : ℕ)
        (Xo : (i : ℕ) → V → Site (X.family.side i p))
        (U : (i : ℕ) → Rooms.Wallet Ω (Xo i) (x i) B ξ qd b)
        (w : V → ℝ) (cost : B.Mode → ℝ), Spirit cost → (∀ i, 0 < w i) →
        Delivered X ζ H ξ b (Emissions.rent w cost) Xo (Studio.speculum X δ qd z) U z
          (N := N) (j := j) (δ := δ) →
        TestedAt (priceNormalized cost (U m).other) (x m).p w
          (Hull.divisor X.alloy.B.a m) ((Real.exp 1 + 1) * Studio.target δ qd (X.T.history N p z).beta)
          (Hull.divisor X.alloy.B.a m * (Coat.gStep (X.T.history N p (m + 1)).beta) ^ e) := by
  filter_upwards [Fees.chosen (X := X) (ζ := ζ) (H := H) (g := hG) B e qd horder hδ hH hζ,
    Hull.always_close (A := X.alloy) hG length] with z hfees hclose
  intro p N j m hz hm hend x ξ b Xo U w cost hcost hw delivered
  exact Delivered.independent_readings X w cost hcost hw rfl hz hm rfl (hclose j hend) hfees delivered

end YM.Qlocal.Actual.Season.Studio
