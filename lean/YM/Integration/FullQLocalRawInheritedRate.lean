import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.CappedRegularGrowth

/-! Raw inherited-error rates retained from the full qlocal proof.
The singleton term contains inverse monitor decay, not a fixed positive
coupling power. The receipt below belongs to one supplied price family;
it chooses no Grant, Run, model, input, or output. Its finite numerical
requests are available before the original block/clock construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.RawInherited
open Filter Lattice Wilson RG Marker
open FullQLocal.RenderedStep
open scoped BigOperators Topology

variable {G : Gauge} {V : Type}

/-- Only the three fixed requested norm parameters enter a zero-alpha bill. -/
def requestedNorm (J : Request V) : BudgetPoint where
  power := J.outputDistanceOrder
  order := J.outputFieldOrder
  supportExponent := J.outputSupport
  B := 1
  threshold := 1
  power_ge := J.distance_minimum
  order_ge := J.field_minimum
  exponent_pos := J.output_support_pos
  B_pos := by decide
  threshold_pos := by norm_num
  threshold_le := le_rfl

/-- A positive pre-length majorant of the complete requested extraction bill. -/
def profileCost (G : Gauge) (J : Request V) (s : Stage) : Real :=
  1 + |CappedRegularReset.regularNeed G (requestedNorm J) s.clip s.width s.paths 0 1|

theorem profileCost_pos (G : Gauge) (J : Request V) (s : Stage) :
    0 < profileCost G J s := by
  unfold profileCost
  positivity

/-- A finite prefix also covers the preceding profile at a stage transition. -/
def profileCover (G : Gauge) (J : Request V) (s : Nat → Stage) (i : Nat) : Real :=
  1 + ∑ k ∈ Finset.range (i + 1), profileCost G J (s k)

theorem profileCost_le_cover (G : Gauge) (J : Request V) (s : Nat → Stage)
    (i j : Nat) (hji : j ≤ i) :
    profileCost G J (s j) ≤ profileCover G J s i := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.range (i + 1)) => (profileCost_pos G J (s k)).le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hji))
  unfold profileCover
  linarith

/-- This is the original norm bill; cover size and threshold are not changed. -/
theorem extraction_le {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : Nat) :
    CappedRegularReset.regularNeed G (A.outputNorm m)
      (C.path.levels.params m).clip (C.path.levels.params m).width
      (C.path.levels.params m).paths 0 1 ≤
      profileCost G J (C.path.levels.params m) := by
  rw [CappedRegularGrowth.regular_fields G (A.outputNorm m) (requestedNorm J)
    (C.path.levels.params m).clip (C.path.levels.params m).width
    (C.path.levels.params m).paths 1 (A.output_norm m).distance
    (A.output_norm m).order (A.output_norm m).reserve]
  exact (le_abs_self _).trans (by unfold profileCost; linarith)

/-- The principal singleton and all remaining polynomial inherited terms. -/
def shape (A : Calendar G) (d m : Nat) : Real :=
  (1 + (A.coverSize m : Real)) ^ d *
      (A.threshold m + (A.monitor m)⁻¹ ^ 2) +
    (1 + (A.coverSize m : Real) + A.monitor m + A.loopCap m) ^ d *
      A.hatCoupling m

/-- The manuscript rate on an already supplied K. The coefficient function
is selected before the block sequence; no weighted conclusion is assumed. -/
structure Receipt {C : Family G} {J : Request V} {A : NumericSchedule C J}
    (K : NumericPrices A) (d : Nat) (post : (Nat → Nat) → Nat → Real) : Prop where
  eventually_bound : ∃ first : Nat, ∀ m, first ≤ m →
    K.vanishing m ≤
      |post (fun i => (C.path.levels.clock.factor i).val)
        (C.path.levels.clock.J (m + 1))| *
      (shape C.path.levels.clock d m + shape C.path.levels.clock d (m + 1))

/-- Preserve the old request and add only the finite extraction invoice. -/
def preRequest (G : Gauge) (J : Request V) (s : Nat → Stage)
    (old : Nat → Real) (i : Nat) : Real :=
  max |old i| (profileCover G J s i)

theorem preRequest_covers (G : Gauge) (J : Request V) (s : Nat → Stage)
    (old : Nat → Real) (i : Nat) :
    profileCover G J s i ≤ |preRequest G J s old i| :=
  (le_max_right _ _).trans (le_abs_self _)

theorem preRequest_preserves (G : Gauge) (J : Request V) (s : Nat → Stage)
    (old : Nat → Real) (i : Nat) : |old i| ≤ |preRequest G J s old i| :=
  (le_max_left _ _).trans (le_abs_self _)

/-- Preserve every old post-length request and the raw-rate coefficient. -/
def postRequest (old post : (Nat → Nat) → Nat → Real)
    (n : Nat → Nat) (i : Nat) : Real := max |old n i| |post n i|

theorem postRequest_covers (old post : (Nat → Nat) → Nat → Real)
    (n : Nat → Nat) (i : Nat) : |post n i| ≤ |postRequest old post n i| :=
  (le_max_right _ _).trans (le_abs_self _)

theorem postRequest_preserves (old post : (Nat → Nat) → Nat → Real)
    (n : Nat → Nat) (i : Nat) : |old n i| ≤ |postRequest old post n i| :=
  (le_max_left _ _).trans (le_abs_self _)

/-- A pure pre-length floor. The prefix covers either adjacent stage index. -/
def floorRequest (G : Gauge) (J : Request V) (s : Nat → Stage)
    (primary : Real) (old : Nat → Nat) (i : Nat) : Nat :=
  max (old i) (Nat.ceil
    (64 * (2 : Real) ^ ((J.order : Real) + 1 - J.eta) * |primary| *
      profileCover G J s i))

theorem floorRequest_covers (G : Gauge) (J : Request V) (s : Nat → Stage)
    (primary : Real) (old : Nat → Nat) (i : Nat) :
    64 * (2 : Real) ^ ((J.order : Real) + 1 - J.eta) * |primary| *
      profileCover G J s i ≤ (floorRequest G J s primary old i : Real) := by
  unfold floorRequest
  exact (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right (old i) (Nat.ceil
      (64 * (2 : Real) ^ ((J.order : Real) + 1 - J.eta) * |primary| *
        profileCover G J s i))))

theorem floorRequest_preserves (G : Gauge) (J : Request V) (s : Nat → Stage)
    (primary : Real) (old : Nat → Nat) (i : Nat) :
    old i ≤ floorRequest G J s primary old i := le_max_left _ _

end YM.Integration.FullQLocal.RawInherited
end
