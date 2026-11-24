import YM.Integration.FullQLocalCanonicalReceipt

/-!
Select both complete countable request families before one original Run.
They share one native component choice. Pointwise maxima retain both original
floor, pre-length and post-length purchases without reindexing either family.
The two resulting receipts have literally the same sheet, quote and n.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Paired
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open LocalComparison
open scoped Topology

variable {G : Gauge}

/-- Both families use the same native choice, selected only once. -/
structure Choice (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) where
  native : NativeComponentRecipe.Choice s
  first k : Complete.Data hG (B k) (J k) s q native
  second k : Complete.Data hG (B' k) (J' k) s q native

variable {hG : G.Simple} {I : ℕ → Type}
  [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {I' : ℕ → Type} [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
  {B' : ∀ k, Census (I' k)} {J' : ∀ k, Request (I' k)}
  {s : Sheet G} {q : MapPrices}

def Choice.left (P : Choice hG I B J I' B' J' s q) :
    Complete.FamilyChoice hG I B J s q :=
  ⟨⟨P.native, fun k => (P.first k).forget⟩, P.first, fun _ => rfl⟩

def Choice.right (P : Choice hG I B J I' B' J' s q) :
    Complete.FamilyChoice hG I' B' J' s q :=
  ⟨⟨P.native, fun k => (P.second k).forget⟩, P.second, fun _ => rfl⟩

/-- The same full manuscript hypothesis supplies both families before R. -/
theorem available (H : Complete.ManuscriptApplication G) (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) :
    Nonempty (Choice hG I B J I' B' J' s q) := by
  let native := Classical.choice (NativeComponentRecipe.available hG s)
  exact ⟨⟨native,
    fun k => Complete.chooseData H hG (B k) (J k) s q native,
    fun k => Complete.chooseData H hG (B' k) (J' k) s q native⟩⟩

def extra (P : Choice hG I B J I' B' J' s q) (i : ℕ) : ℕ :=
  max (PreRun.extra P.left.resource i) (PreRun.extra P.right.resource i)

def numeric (P : Choice hG I B J I' B' J' s q) (k i : ℕ) : ℝ :=
  max |PreRun.numeric P.left.resource k i| |PreRun.numeric P.right.resource k i|

def postnumeric (P : Choice hG I B J I' B' J' s q)
    (lengths : ℕ → ℕ) (k i : ℕ) : ℝ :=
  max |PreRun.postnumeric P.left.resource lengths k i|
    |PreRun.postnumeric P.right.resource lengths k i|

/-- Both receipts are on one R, with the same physical construction data. -/
structure Receipt (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k)) (R : Run G) where
  left : PreRun.Receipt hG I B J R
  right : PreRun.Receipt hG I' B' J' R
  left_complete : Complete.Attachment left
  right_complete : Complete.Attachment right
  same_sheet : left.sheet = right.sheet
  same_quote : left.quote = right.quote
  same_n : left.n = right.n
  same_native : HEq left.chosen.native right.chosen.native

private theorem paid_mono {F K : ℕ → ℕ → ℝ} {A : Levels G}
    (h : ∀ k i, |F k i| ≤ |K k i|)
    (hK : NativeDiagonalClockRequest.PaidRequests K A) :
    NativeDiagonalClockRequest.PaidRequests F A := by
  refine ⟨hK.1, ?_⟩
  intro k
  obtain ⟨first, hf⟩ := hK.2 k
  exact ⟨first, fun m hm i hi => (h k i).trans (hf m hm i hi)⟩

/-- Project both purchased families without choosing or reconstructing R. -/
theorem receipt_of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (Choice hG I B J I' B' J')
      (fun _ _ P => extra P) (fun _ _ P => numeric P)
      (fun _ _ P => postnumeric P) R) :
    Nonempty (Receipt hG I B J I' B' J' R) := by
  rcases h with ⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩
  have hel : PreRun.extra P.left.resource ≤ n := by
    intro i
    exact (le_max_left _ _).trans (he i)
  have her : PreRun.extra P.right.resource ≤ n := by
    intro i
    exact (le_max_right _ _).trans (he i)
  have hnl : NativeDiagonalClockRequest.PaidRequests
      (PreRun.numeric P.left.resource) R.family.path.levels := by
    apply paid_mono (hK := hn)
    intro k i
    exact (le_max_left _ _).trans (le_abs_self _)
  have hnr : NativeDiagonalClockRequest.PaidRequests
      (PreRun.numeric P.right.resource) R.family.path.levels := by
    apply paid_mono (hK := hn)
    intro k i
    exact (le_max_right _ _).trans (le_abs_self _)
  have hpl : NativeDiagonalClockRequest.PaidRequests
      (PreRun.postnumeric P.left.resource
        (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels := by
    apply paid_mono (hK := hp)
    intro k i
    exact (le_max_left _ _).trans (le_abs_self _)
  have hpr : NativeDiagonalClockRequest.PaidRequests
      (PreRun.postnumeric P.right.resource
        (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels := by
    apply paid_mono (hK := hp)
    intro k i
    exact (le_max_right _ _).trans (le_abs_self _)
  have htl : NativePostLengthPayment.StagePaid
      (PreRun.postnumeric P.left.resource
        (fun i => (R.family.path.levels.clock.factor i).val) 0) R.family.path.levels := by
    intro m
    exact ((le_abs_self _).trans (le_max_left _ _)).trans (ht m)
  have htr : NativePostLengthPayment.StagePaid
      (PreRun.postnumeric P.right.resource
        (fun i => (R.family.path.levels.clock.factor i).val) 0) R.family.path.levels := by
    intro m
    exact ((le_abs_self _).trans (le_max_right _ _)).trans (ht m)
  let left := Complete.receipt P.left n hb hel hs hq hnl hpl htl
  let right := Complete.receipt P.right n hb her hs hq hnr hpr htr
  exact ⟨⟨left, right,
    Complete.Attachment.of_entries left P.left.entry P.left.entry_eq,
    Complete.Attachment.of_entries right P.right.entry P.right.entry_eq,
    rfl, rfl, rfl, HEq.rfl⟩⟩

end YM.Integration.FullQLocal.PreRun.Paired
end
