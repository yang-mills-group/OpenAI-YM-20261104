import YM.Integration.UniformCoefficientEnvelope
import YM.RemainderComparison.Typeface.Press
import YM.RemainderComparison.Creek.Icing

/-! Concrete use of the RG01 common-price supplier for independently chosen tests.
The original analytic/model admission hypotheses are retained verbatim. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open RemainderComparison
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open RemainderComparison RemainderComparison.Typeface
open RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif

variable {ι : Type} {α : ι → Type*}
variable {G : Gauge} {c f : Side} {R : Rep G f}

/-- Each slot reads its own test coordinate; costs and roots stay fixed. -/
def independentPortraits (M : ∀ i, Portrait R (α i)) :
    ι → Portrait R (∀ i, α i) := fun i =>
  { wing := (M i).wing
    weight := (M i).weight
    angle := fun tests => (M i).angle (tests i)
    turned := fun tests => (M i).turned (tests i)
    budget := fun tests => (M i).budget (tests i) }

@[simp] theorem independent_angle (M : ∀ i, Portrait R (α i))
    (tests : ∀ i, α i) (i : ι) :
    (independentPortraits M i).angle tests = (M i).angle (tests i) := rfl

variable {L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {W x μ C a d e K σ Y γ V T0 τ : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
    {j k s J I : ℕ}
variable (H : Cash W x μ L Q o C T R) (χ : Chi) (U : Pad H j χ)
variable (M : ∀ i, Portrait R (α i)) (tests₀ : ∀ i, α i)
    (l : ι → ℝ) (Z : Set ι) (δ : ℝ)

variable (h : Roles H χ U k s J I a d e K σ Y γ V T0)
    (hh : Motto (brand (independentPortraits M) tests₀) l δ H τ K Y I)
    (P' : BudgetPoint) (hB : P'.B = radiusB x)
    (hthreshold : P'.threshold = Pressure.temp x)
    (horder : P'.order ≤ j) (hpower : P'.power ≤ J)

include h hh hB hthreshold horder hpower

/-- The actual high-cluster coefficient family has a joint independent-test and
field-derivative supremum *inside* its weighted activity norm, at the supplier's
unchanged coupling power. The family remains `Creek.theater` on the same `R`. -/
theorem actual_high_uniform_jet_cost :
    (∀ i, 0 ≤ jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) ({p : Staff (brand (independentPortraits M) tests₀) H | Pure (brand (independentPortraits M) tests₀) H χ Z k p ∧ tumble H p.1}) P' i) ∧
    (∀ i ∈ ({p : Staff (brand (independentPortraits M) tests₀) H | Pure (brand (independentPortraits M) tests₀) H χ Z k p ∧ tumble H p.1}), ∀ tests root, root ∈ ((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls i →
      P'.supBounds root (((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls i) (((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).solvent tests i) (jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) ({p : Staff (brand (independentPortraits M) tests₀) H | Pure (brand (independentPortraits M) tests₀) H χ Z k p ∧ tumble H p.1}) P' i)) ∧
    Ac.Hit ((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls P'.B (jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) ({p : Staff (brand (independentPortraits M) tests₀) H | Pure (brand (independentPortraits M) tests₀) H χ Z k p ∧ tumble H p.1}) P') a ((gStep R.beta)^s) := by
  apply spinal_jet_cost
  apply Creek.prior (H := H) (χ := χ) (M := (independentPortraits M)) (x' := tests₀)
    (l := l) (Z := Z) (δ := δ) (P' := P')
  intro tests
  exact (Typeface.ally (H := H) (χ := χ) (U := U) (M := (independentPortraits M))
    (x' := tests₀) (y := tests) (l := l) (Z := Z) (δ := δ)
    (h := h) (hh := hh) (P' := P')
    (hx := hB) (hp := hthreshold) (ht := horder) (hk := hpower)).1

variable (E : Set ℕ) (n : ℕ) (w : ℕ → ℝ)
    (hcost : Sleet.Cost R E n x d σ w)
    (hpale : Muse.Pale (brand (independentPortraits M) tests₀) Z l n d τ K I H)
    (kept : Set (Staff (brand (independentPortraits M) tests₀) H))
    (hlow : Creek.Lowers H χ (independentPortraits M) tests₀ l Z δ E n k s kept)
    {z C₀ T₁ : ℝ}
    (hsolo : Solo.Supply H χ E P' z C₀) (hz : z ≤ a)
    (wp : ℕ → ℝ) (hhalo : Halo.Presents R E wp T₁)
    (hsmall : T₁ ≤ incomingE G L x)

include hcost hpale hlow hsolo hz hhalo hsmall

/-- The complete omitted-sector supplier pays the joint test/derivative
coefficient envelope. Its structural low-sector admission and analytic
supplier inputs are explicit; no uniform-remainder estimate is assumed. -/
theorem actual_omitted_uniform_jet_cost :
    (∀ i, 0 ≤ jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) (Creek.Academy H χ (independentPortraits M) tests₀ l Z δ k \ kept) P' i) ∧
    (∀ i ∈ (Creek.Academy H χ (independentPortraits M) tests₀ l Z δ k \ kept), ∀ tests root, root ∈ ((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls i →
      P'.supBounds root (((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls i) (((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).solvent tests i)
        (jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) (Creek.Academy H χ (independentPortraits M) tests₀ l Z δ k \ kept) P' i)) ∧
    Ac.Hit ((Creek.theater H χ (independentPortraits M) tests₀ l Z δ)).halls P'.B (jetCost (Creek.theater H χ (independentPortraits M) tests₀ l Z δ) (Creek.Academy H χ (independentPortraits M) tests₀ l Z δ k \ kept) P') z
      (4 * (gStep R.beta)^s + V * T₁ + Y^k * Y * γ * δ) := by
  apply spinal_jet_cost
  exact (Creek.sheen H χ U (independentPortraits M) tests₀ l Z δ h hh P'
    hB hthreshold horder hpower E n w hcost hpale hlow
    hsolo hz wp hhalo hsmall).1

end YM.Integration
