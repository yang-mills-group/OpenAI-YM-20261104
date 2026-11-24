import YM.Integration.FVA1Physical.MixedResets.CoverStep
import YM.QuadraticLocal.Fk.Guild

/-!
# Per-ray and per-row interpretation of the printed curvature packets

Pass from formal projection on each pinned Club to an identity on the CONSTRUCTED analytic
kernel bank. Spectator probes can be passed inside these sums. Makes no summability or
priority demands on omitting/truncating real clusters. `Renderer` uses an actual `Row`
on its physical support, not a pointwise completion of a formal jet.

`seam_tally` later relates the complete bill to the finite Wick pin step. Note that for
**global** (i.e. clear, already field-independent) inputs the passthrough rule of `coverStep`
does not need to calculate a winding correction at all (`ScatterR.total` is a finite-volume
exact identity on these inputs). The forecast still emits field-independent coefficients from
nontrivial inputs: no global marks are being subtracted at normalization.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Filter Function Finset Lattice RG Wilson Marker Precision Tree Input
open Push Uniform Next.SectorChange
open Comparison.RG02
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open scoped Classical Topology BigOperators ContDiff

variable {G : Gauge} {c : Side} {V : Type} [Fintype V] [DecidableEq V]
    {I : Marker.Census V} {ι ι' α : Type} {passport' : Passport c V}

/-- Unmasked Colors of the actual given bank. -/
def colorsOf (rows : ι' → Row passport' I G α) (U : Layout G) (extra : Finset Age)
    (grades : V → ℕ) (t : α) := Air.craft rows (fun i => (rows i).paint t) grades U extra

/-- One literal bank of these coefficients. Includes global marks unscaled from any
preimage coupling; the power account is already in `Income` data. Renderer uses the
nonlinear curvature completions even above the orders read back. The paid `Press` below is a
specific, independently purchased such render, not freely chosen after the actual RG step. -/
structure Renderer (rows : ι' → Row passport' I G α) (U : Layout G) (extra : Finset Age)
    (grades : V → ℕ) (p : ℕ) (bill : ℕ → α → rule (Coarse G) c → Poly I) : Prop where
  whole (t : α) (x : Config G c) (g : ℝ) (hn : g ≠ 0) :
    HasSum (fun i => Poly.send (rows i).mode ((rows i).nominal g t x))
      (Comparison.RG02.Integral.markedLog g x (colorsOf rows U extra grades t))
  coefficients (r : ℕ) (hr : r ≤ p) (t : α) (z : rule (Coarse G) c) :
    Air.discharge (colorsOf rows U extra grades t) r (tint G (Exterior.Body 1 c) (exteriorL G c z)) = bill r t z
  realizes (r : ℕ) (hr : r ≤ p) (t : α) (z : rule (Coarse G) c) :
    HasSum (fun i => Poly.send (rows i).mode ((rows i).paint t * (↑((rows i).markReceipt r z) : ℂ))) (bill r t z)

theorem renderer_from_discharge {rows : ι' → Row passport' I G α}
    {U : Layout G} {extra : Finset Age} {grades : V → ℕ} {weights : V → ℝ} {funds width : ℝ} {p pieces k : ℕ}
    (paid : Earn.Scene.Armada rows weights grades width funds p pieces k)
    (positive : 0 < width) {bill : ℕ → α → rule (Coarse G) c → Poly I}
    (matches_bill : ∀ (r : ℕ), r ≤ p → ∀ t z,
      Air.discharge (colorsOf rows U extra grades t) r (tint G (Exterior.Body 1 c) (exteriorL G c z)) = bill r t z) :
    Renderer rows U extra grades p bill := by
  have cap (t : α) := Air.license rows (fun i => (rows i).paint t) grades weights paid positive
    (fun i => paid.honor i t)
  refine ⟨fun t x g hg => ?_, matches_bill, fun r order t z => ?_⟩
  · exact Air.liftPassport rows _ grades (cap t) U extra g hg x
  rw [← matches_bill _ order]
  exact Air.compared rows _ grades (cap t) U extra z r

variable {f : Side} {S : StepData c f} {O : ChartRatio G}
    {action : PathData G} {clip : Clip} {U : Layout G} {extra : Finset Age} {p : ℕ}
    {passport : Passport f V}
    (M : ι → Row passport I G α)

set_option quotPrecheck false
local notation "bill" => coverStep S O action clip U extra M
local notation "club" => clubOutput S O action clip U extra M

variable (X : Press M p)

/-- Certificate on EACH disjoint Club of the Publisher. Deterministic interpretation before
applying it to an actual marked density. -/
def PressWrites (S : StepData c f) (O : ChartRatio G) (action : PathData G) (clip : Clip)
    (U : Layout G) (extra : Finset Age) : Prop :=
  ∀ (u : Club M) (r : ℕ), r ≤ p → ∀ (z : rule (Coarse G) c),
    Alliance.seen M S.ratio z X r u = clubCoefficient S O action clip U extra M u p r z

variable {U' : Layout G} {extra' : Finset Age}
  (h : PressWrites M X S O action clip U extra)
  {grades : V → ℕ} {weights : V → ℝ} {funds width a e : ℝ} {pieces k : ℕ}
  (L : Press.Receipt M X a e)

local notation "letters" => Earn.Scene.letters M S.ratio X L width
include h

omit [Fintype V] in
theorem cluster_eq (r : ℕ) (order : r ≤ p) (t : α) (z : rule (Coarse G) c) :
    (Eden.clusters M S.ratio X t z r) = club p r t z := by
  funext u
  unfold Eden.clusters clubOutput
  rw [← h u r order z]
  rfl

omit [Fintype V] in
theorem press_per_group (r : ℕ) (order : r ≤ p) (u : Club M) (t : α) (z : rule (Coarse G) c)
    (hl : 0 < a) :
    HasSum (fun j : Press.Palette M S.ratio X u =>
        Eden.paving M S.ratio X L width t z r (Sum.inr (⟨u,j⟩ : Press.Runway M S.ratio X)))
      (club p r t z u) := by
  rw [← cluster_eq M X h r order]
  exact Eden.elite M S.ratio u X L width hl t z r

variable (paid : Earn.Scene.Armada (Earn.Scene.letters M S.ratio X L width) weights grades width funds p pieces k)
include L paid
set_option maxHeartbeats 400000

theorem printed_discharge (hw : 0 < width) (ha : 0 < a) (r : ℕ) (order : r ≤ p) (t : α)
    (z : rule (Coarse G) c) :
    Summable (club p r t z) ∧ Summable (globalOutput M r t) ∧
    Air.discharge (colorsOf letters U' extra' grades t) r (tint G (Exterior.Body 1 c) (exteriorL G c z)) = bill p r t z := by
  unfold coverStep
  rw [← cluster_eq M X h r order]
  exact Eden.assembled M S.ratio grades weights X L width funds paid hw ha t z U' extra' r

theorem press_renders (hw : 0 < width) (ha : 0 < a) :
    Renderer letters U' extra' grades p (bill p) :=
  renderer_from_discharge paid hw
    (fun r order t z => (printed_discharge M X h L paid hw ha r order t z).2.2)
end YM.Integration.FVA1Physical.MixedResets
