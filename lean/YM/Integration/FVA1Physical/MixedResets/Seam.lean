import YM.Integration.FVA1Physical.MixedResets.Binding

/-!
# Exact club superposition: adapter also to the *working finite-volume* Fk

This layer deliberately does NOT claim matching of this extra seam term in full support
norm — `coverStep` is precisely the cover version of Fk for local comparison,
and the represented difference will be to the packets of *that*. Seam price, as also in
`Oak.Tutoring.Unearthed`, is for additional use on periodized comparisons in
ordinary field jets. Keep this seam invoice even in the summed chart quantities there.

It proves in particular that `coverStep` uses exactly the Club superposition of
`RG02.Bulk.Fk`, EXTENDED to countably many rows; clear entries correctly bypass
with no finite volume correction. Thus no analytic conjecture about reproducing a masked
or clipped finite gauge integral enters the independent reference.
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
variable {G : Gauge} {c f : Side} {V : Type} [Fintype V] [DecidableEq V]
   {I : Marker.Census V} {ι α : Type} {S : StepData c f}
   {passport : Passport f V} (M : ι → Row passport I G α)
   {O : ChartRatio G} {action : PathData G} {clip : Clip} {U : Layout G} {extra : Finset Age}

variable {g : Bulk.Kernel S clip action O} {F : Forest S.ratio} {tag : S.Choices} {z : rule (Coarse G) c}
  {p r : ℕ} (t : α) {U' : Layout G} {e : Finset Age} {grades : V → ℕ}
set_option quotPrecheck false
local notation "Φ" => tint G (Exterior.Body 1 c) (exteriorL G c z)
local notation "paint" => (fun i=> (M i).paint t)
local notation "ζ" => coverStep S O action clip U extra M p r t z
local notation "π" => clubOutput S O action clip U extra M p r t z
local notation "hp" => colorsOf M U extra grades t
local notation "hk" => Bulk.Fk g F tag hp Φ p
local notation "step" => Order.observe I p (Order.logMarked hk) r
local notation "τm" => ScatterR.unitTerm M U extra g F tag Φ (fun i=>(M i).paint t) r p

variable (X : Press M p) (h : PressWrites M X S O action clip U extra) (order : r ≤ p)
local notation "J" => Alliance.miss M paint S.ratio g F tag z U extra X r
include h order
omit [Fintype V] in
lemma seam_diff : Alliance.miss M paint S.ratio g F tag z U extra X r = τm - π := by
  ext1 u
  apply eq_sub_of_add_eq
  rw [← cluster_eq M X h r order t z, Guild.moment_charge M S X g F tag z U extra t]
  rfl


/-- If the analytic printer and seam cost have both been paid, obtain this ADDITIONAL
finite-volume club assembly identity as well as the seam-inclusive comparison.
The hypotheses supplied by the CP5 bank are `hpays` (on the actual card),
`render`, `h`, `Left` (from Armada/printer) and `seam`, all proved separately. -/
lemma seam_tally {δ : Poly I} (seam : HasSum J δ) {N : Type} {pass : Passport c V}
    {rows : N → Row pass I G α}
    (render : Renderer rows U' e grades p (coverStep S O action clip U extra M p))
    (Left : Summable π) (Right : Summable (globalOutput M r t))
    (hpays : step = Air.discharge (colorsOf rows U' e grades t) r Φ + δ) :
    step = ζ + δ ∧ HasSum τm ((∑' u : Club M, π u) + δ) ∧
    HasSum (Sum.elim τm (globalOutput M r t) : Club M ⊕ Solo.Watching M → Poly I) step := by
  rw [render.coefficients r order t z] at hpays
  have seen := seam_diff M t X h order (tag:=tag) (z:=z) (g:=g) (F:=F)
  have sum : HasSum τm ((∑' u : Club M, π u) + δ) := by
    rw [show τm= π + J by rw [seen]; abel]
    exact Left.hasSum.add seam
  refine ⟨hpays, sum, ?_⟩
  have eqn := sum.sum (f:=Sum.elim (β:=Solo.Watching M) τm (globalOutput M r t)) Right.hasSum
  rw [hpays, coverStep, add_right_comm]
  exact eqn
end YM.Integration.FVA1Physical.MixedResets
