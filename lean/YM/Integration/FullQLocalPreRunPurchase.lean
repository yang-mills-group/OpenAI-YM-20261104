import YM.Integration.FullQLocalPreRunApplication
import YM.Integration.NativeDiagonalFloorRequest
import YM.Integration.ActualCountableWidthPayment

/-!
Constructive purchase of the already selected full-q floors and widths.
A countable family is fixed before the single native Run construction.
At each profile only a finite prefix of floors is imposed. Every fixed
request then has its own common tail, before all physical periods and data.
All original native component requests are retained in the same payload.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric.Retained
open LocalComparison
open scoped Topology

variable {G : Gauge}

/-- Native component data and all finite qlocal choices precede the Run. -/
structure FamilyChoice (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (s : Sheet G) (q : MapPrices) where
  native : NativeComponentRecipe.Choice s
  entry k : Data hG (B k) (J k) s q native

variable {hG : G.Simple} {I : ℕ → Type}
  [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {s : Sheet G} {q : MapPrices}

/-- Countable selection uses the same supplied finite-request hypothesis. -/
theorem family_available (H : ManuscriptApplication G) (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (s : Sheet G) (q : MapPrices) :
    Nonempty (FamilyChoice hG I B J s q) := by
  let native := Classical.choice (NativeComponentRecipe.available hG s)
  exact ⟨⟨native, fun k => Classical.choice (H hG (I k) (B k) (J k) s q native)⟩⟩

def extra (P : FamilyChoice hG I B J s q) (i : ℕ) : ℕ :=
  max (NativeComponentRecipe.floor s q P.native i)
    (NativeDiagonalFloorRequest.diagonalFloor s.floorL (fun k => (P.entry k).floor) i)

def numeric (P : FamilyChoice hG I B J s q) (k i : ℕ) : ℝ :=
  max |NativeComponentRecipe.numeric s q P.native k i|
    (max |((P.entry k).widths.width i)⁻¹| |(P.entry k).preRequest i|)

def postnumeric (P : FamilyChoice hG I B J s q)
    (lengths : ℕ → ℕ) (k i : ℕ) : ℝ :=
  max |NativeComponentRecipe.post s q P.native lengths i|
    |(P.entry k).postRequest lengths i|

/-- This is exactly the payload retained by the one native preselection. -/
structure Receipt (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k)) (R : Run G) where
  sheet : Sheet G
  quote : MapPrices
  chosen : FamilyChoice hG I B J sheet quote
  n : ℕ → ℕ
  base_le : sheet.floorL ≤ n
  extra_le : extra chosen ≤ n
  sheet_eq : R.metals.p = ThroughLaunch.raise sheet n
  quote_eq : R.metals.K = ThroughLaunch.raging sheet quote
  numeric_paid : NativeDiagonalClockRequest.PaidRequests (numeric chosen)
    R.family.path.levels
  post_paid : NativeDiagonalClockRequest.PaidRequests
    (postnumeric chosen (fun i => (R.family.path.levels.clock.factor i).val))
    R.family.path.levels
  stage_paid : NativePostLengthPayment.StagePaid
    (postnumeric chosen (fun i => (R.family.path.levels.clock.factor i).val) 0)
    R.family.path.levels

theorem receipt_of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (FamilyChoice hG I B J)
      (fun _ _ P => extra P) (fun _ _ P => numeric P)
      (fun _ _ P => postnumeric P) R) :
    Nonempty (Receipt hG I B J R) := by
  rcases h with ⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩
  exact ⟨⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩⟩

private theorem paid_mono {F K : ℕ → ℕ → ℝ} {A : Levels G}
    (h : ∀ k i, |F k i| ≤ |K k i|)
    (hK : NativeDiagonalClockRequest.PaidRequests K A) :
    NativeDiagonalClockRequest.PaidRequests F A := by
  refine ⟨hK.1, ?_⟩
  intro k
  obtain ⟨first, hf⟩ := hK.2 k
  exact ⟨first, fun m hm i hi => (h k i).trans (hf m hm i hi)⟩

variable {R : Run G} (r : Receipt hG I B J R)

private theorem native_floor :
    NativeComponentRecipe.floor r.sheet r.quote r.chosen.native ≤ r.n := by
  intro i
  exact (le_max_left _ _).trans (r.extra_le i)

private theorem native_stage : NativePostLengthPayment.StagePaid
    (NativeComponentRecipe.post r.sheet r.quote r.chosen.native
      (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels := by
  intro m
  exact ((le_abs_self _).trans (le_max_left _ _)).trans (r.stage_paid m)

include r in
/-- All earlier component requests survive the enlarged preselection. -/
theorem native_preselection :
    R2I.RG05Joint.PostnumericPreselection
      (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s)
      NativeComponentRecipe.floor NativeComponentRecipe.numeric
      ActualRunNativeComponentRecipe.postnumeric R := by
  refine ⟨r.sheet, r.quote, r.chosen.native, r.n, r.base_le,
    native_floor r, r.sheet_eq, r.quote_eq, ?_, ?_, native_stage r⟩
  · apply paid_mono (hK := r.numeric_paid)
    intro k i
    exact (le_max_left _ _).trans (le_abs_self _)
  · apply paid_mono (hK := r.post_paid)
    intro k i
    exact (le_max_left _ _).trans (le_abs_self _)

/-- The same original Horizon and Levels realize the native component data. -/
theorem component : NativeComponentRecipe.Realized r.sheet r.quote r.chosen.native
    R.family.path.levels R.alloy.B.M :=
  ActualRunNativeComponentRecipe.on_run R r.sheet r.quote r.chosen.native r.n
    r.sheet_eq r.quote_eq (native_floor r) (native_stage r)

include r in
theorem attached : ActualRunNativeComponentRecipe.Attached R :=
  ActualRunNativeComponentRecipe.of_preselection R (native_preselection r)

theorem widths_paid : ActualCountableWidthPayment.PaidWidths
    (fun k => (r.chosen.entry k).widths) R.family.path.levels := by
  apply paid_mono (hK := r.numeric_paid)
  intro k i
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_abs_self _)

def width_payment (k : ℕ) : WidthPayment R.family (r.chosen.entry k).widths :=
  ActualCountableWidthPayment.payment
    (fun j => (r.chosen.entry j).widths) R.family (widths_paid r) k

theorem pre_paid (k : ℕ) :
    PaidProfile (r.chosen.entry k).preRequest R.family.path.levels := by
  obtain ⟨first, hf⟩ := r.numeric_paid.2 k
  refine ⟨first, ?_⟩
  intro m hm i hi
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans
    ((le_abs_self _).trans (hf m hm i hi))

theorem post_request_paid (k : ℕ) :
    PaidProfile
      ((r.chosen.entry k).postRequest (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels := by
  obtain ⟨first, hf⟩ := r.post_paid.2 k
  refine ⟨first, ?_⟩
  intro m hm i hi
  exact (le_max_right _ _).trans ((le_abs_self _).trans (hf m hm i hi))

/-- Both actual adjacent profile floors are paid after each fixed request. -/
theorem floors_eventually (k : ℕ) :
    ∃ first : ℕ, ∀ m, first ≤ m →
      (r.chosen.entry k).floor (R.family.path.levels.clock.J m) ≤
        r.n (R.family.path.levels.clock.J m) ∧
      (r.chosen.entry k).floor (R.family.path.levels.clock.J (m+1)) ≤
        r.n (R.family.path.levels.clock.J (m+1)) := by
  obtain ⟨first, hf⟩ := NativeDiagonalFloorRequest.pair_eventually
    r.sheet.floorL (fun j => (r.chosen.entry j).floor) R.family.path.levels k
  refine ⟨first, ?_⟩
  intro m hm
  exact ⟨(hf m hm).1.trans ((le_max_right _ _).trans (r.extra_le _)),
    (hf m hm).2.trans ((le_max_right _ _).trans (r.extra_le _))⟩

/-- The tail precedes every Datum, cutoff and period for the fixed request. -/
theorem local_floors (k : ℕ) :
    ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family (B k), first ≤ d.level →
      Handoff.LocalFloors (r.chosen.entry k).floor r.n d := by
  obtain ⟨first, hf⟩ := floors_eventually r k
  exact ⟨first, fun d hd => hf d.level hd⟩

/-- A genuine Grant at the literal purchased schedule, on the same Run.
Only the named manuscript hypothesis stored in the preselected entry is used. -/
def grant (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (k : ℕ) (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Grant (R := B k) (r.chosen.entry k).capacities (RunFormalChain.fromRun R) (J k)
      (ActualRequestNumericSchedule.selected R hG hReadout
        (r.chosen.entry k).widths (width_payment r k) (J k) cap hcap hcap0)
      (r.chosen.entry k).floor r.n (r.chosen.entry k).constant :=
  Classical.choice ((r.chosen.entry k).grant r.n r.base_le R r.sheet_eq r.quote_eq
    (component r) hReadout (width_payment r k) (pre_paid r k) (post_request_paid r k)
    cap hcap hcap0)

end YM.Integration.FullQLocal.PreRun
end
