import YM.Integration.FullQLocalCostProfileChain
import YM.Integration.NativeDiagonalFloorRequest
import YM.Integration.ActualCountableWidthPayment

/-!
Resource receipts for the new cost-profile data. These records contain only
the purchased widths and scalar requests, so no analytic Grant is manufactured
when a larger cost recipe is selected.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open Profile
open scoped Topology

structure Resources where
  widths : ProfileWidths
  floor : ℕ → ℕ
  preRequest : ℕ → ℝ
  postRequest : (ℕ → ℕ) → ℕ → ℝ

variable {G : Gauge}

def Data.resources {V : Type} [DecidableEq V] [Fintype V]
    {hG : G.Simple} {B : Census V} {J : Request V}
    {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}
    {caps : Handoff.OutputCapacities} {D : Diagram s q native}
    {W : Allocation D} {e : Recipe}
    (E : Data hG B J s q native caps D W e) : Resources where
  widths := W.input
  floor := E.purchases.floor J s
  preRequest := E.purchases.pre J W
  postRequest := E.purchases.post

def Resources.extra (base : ℕ → ℕ) (F : ℕ → Resources) : ℕ → ℕ :=
  NativeDiagonalFloorRequest.diagonalFloor base (fun k => (F k).floor)

def Resources.numeric (F : ℕ → Resources) (k i : ℕ) : ℝ :=
  max |((F k).widths.width i)⁻¹| |(F k).preRequest i|

def Resources.postnumeric (F : ℕ → Resources) (lengths : ℕ → ℕ)
    (k i : ℕ) : ℝ :=
  (F k).postRequest lengths i

structure Resources.Receipt (F : ℕ → Resources) (R : Run G)
    (base n : ℕ → ℕ) where
  extra_le : Resources.extra base F ≤ n
  numeric_paid : NativeDiagonalClockRequest.PaidRequests (Resources.numeric F)
    R.family.path.levels
  post_paid : NativeDiagonalClockRequest.PaidRequests
    (Resources.postnumeric F (fun i => (R.family.path.levels.clock.factor i).val))
    R.family.path.levels

variable {F : ℕ → Resources} {R : Run G} {base n : ℕ → ℕ}

theorem Resources.Receipt.widths_paid (p : Resources.Receipt F R base n) :
    ActualCountableWidthPayment.PaidWidths
      (fun k => (F k).widths) R.family.path.levels := by
  refine ⟨p.numeric_paid.1, ?_⟩
  intro k
  obtain ⟨first, hf⟩ := p.numeric_paid.2 k
  refine ⟨first, ?_⟩
  intro m hm i hi
  exact ((le_max_left _ _).trans (le_abs_self _)).trans (hf m hm i hi)

def Resources.Receipt.width_payment (p : Resources.Receipt F R base n) (k : ℕ) :
    WidthPayment R.family (F k).widths :=
  ActualCountableWidthPayment.payment (fun j => (F j).widths)
    R.family (p.widths_paid) k

theorem Resources.Receipt.pre_paid (p : Resources.Receipt F R base n) (k : ℕ) :
    PaidProfile (F k).preRequest R.family.path.levels := by
  obtain ⟨first, hf⟩ := p.numeric_paid.2 k
  refine ⟨first, ?_⟩
  intro m hm i hi
  exact ((le_max_right _ _).trans (le_abs_self _)).trans (hf m hm i hi)

theorem Resources.Receipt.post_request_paid (p : Resources.Receipt F R base n) (k : ℕ) :
    PaidProfile ((F k).postRequest
      (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels :=
  p.post_paid.2 k

theorem Resources.Receipt.floors_eventually (p : Resources.Receipt F R base n) (k : ℕ) :
    ∃ first : ℕ, ∀ m, first ≤ m →
      (F k).floor (R.family.path.levels.clock.J m) ≤
        n (R.family.path.levels.clock.J m) ∧
      (F k).floor (R.family.path.levels.clock.J (m + 1)) ≤
        n (R.family.path.levels.clock.J (m + 1)) := by
  obtain ⟨first, hf⟩ := NativeDiagonalFloorRequest.pair_eventually
    base (fun j => (F j).floor) R.family.path.levels k
  exact ⟨first, fun m hm =>
    ⟨(hf m hm).1.trans (p.extra_le _), (hf m hm).2.trans (p.extra_le _)⟩⟩

end YM.Integration.FullQLocal.PreRun.CostProfile
end
