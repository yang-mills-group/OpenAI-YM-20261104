import YM.Integration.FullQLocalProfileChain
import YM.Integration.FullQLocalTransportedPairedPreRun
import Mathlib.Data.Nat.Pairing

/-!
The two original request families and all their finite successor chains are
purchased before one original Run. Each branch keeps its own exact specification,
allocation and selected grant. Legacy projections never identify independent
analytic choices.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Profile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
  {hG : G.Simple} {B : Census V} {J : Request V}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

/-- One prescribed-width grant together with the raw rate of that same grant. -/
abbrev Chain.Grant (S : Chain hG B J s q native) (r n : ℕ)
    (R : Run G) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family (S.allocation r n).input) (lengths : ℕ → ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :=
  { H : Numeric.Prescribed.Grant (Gamma := B)
      (S.stage r n).selected.capacities (RunFormalChain.fromRun R) (S.stage r n).request
      (ActualRequestNumericSchedule.selected R hG hReadout
        (S.allocation r n).input P (S.stage r n).request cap hcap hcap0)
      ((S.data r n).purchases.floor (S.stage r n).request s) lengths
      (S.data r n).purchases.constant ((S.allocation r n).target R.family) //
    RawInherited.Receipt H.original.models.prices
      (S.data r n).purchases.rawDegree (S.data r n).purchases.rawCoefficient }

end YM.Integration.FullQLocal.PreRun.Profile

namespace YM.Integration.FullQLocal.PreRun.ProfilePaired
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open LocalComparison
open scoped Topology

def index (k r n : ℕ) : ℕ := Nat.pair k (Nat.pair r n)
def seed (i : ℕ) : ℕ := (Nat.unpair i).1
def degree (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).2).1
def depth (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).2).2

theorem index_spec (k r n : ℕ) :
    seed (index k r n) = k ∧ degree (index k r n) = r ∧ depth (index k r n) = n := by
  simp [index, seed, degree, depth]

abbrev Alphabet (I : ℕ → Type) (i : ℕ) := I (seed i)

variable {G : Gauge} {hG : G.Simple}
  {I : ℕ → Type} [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

def chainRequests (C : ∀ k, Profile.Chain hG (B k) (J k) s q native) (i : ℕ) :
    Request (Alphabet I i) :=
  ((C (seed i)).stage (degree i) (depth i)).request

def chainResource (C : ∀ k, Profile.Chain hG (B k) (J k) s q native) :
    PreRun.FamilyChoice hG (Alphabet I) (fun i => B (seed i)) (chainRequests C) s q :=
  ⟨native, fun i => ((C (seed i)).data (degree i) (depth i)).forget.forget⟩

/-- Both legacy families and all successor branches share one native choice. -/
structure Choice (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) where
  legacy : TransportedPaired.Choice hG I B J I' B' J' s q
  first k : Profile.Chain hG (B k) (J k) s q legacy.native
  second k : Profile.Chain hG (B' k) (J' k) s q legacy.native

variable {I' : ℕ → Type} [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
  {B' : ∀ k, Census (I' k)} {J' : ∀ k, Request (I' k)}

def Choice.firstResource (P : Choice hG I B J I' B' J' s q) :=
  chainResource P.first

def Choice.secondResource (P : Choice hG I B J I' B' J' s q) :=
  chainResource P.second

/-- The only analytic input is the full two-stage manuscript specification. -/
theorem available (H : Profile.ManuscriptApplication G) (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) :
    Nonempty (Choice hG I B J I' B' J' s q) := by
  let P := Classical.choice (TransportedPaired.available H.transported hG I B J I' B' J' s q)
  exact ⟨⟨P,
    fun k => Profile.chooseChain H hG (B k) (J k) s q P.native,
    fun k => Profile.chooseChain H hG (B' k) (J' k) s q P.native⟩⟩

def extra (P : Choice hG I B J I' B' J' s q) (i : ℕ) : ℕ :=
  max (TransportedPaired.extra P.legacy i)
    (max (PreRun.extra P.firstResource i) (PreRun.extra P.secondResource i))

def numeric (P : Choice hG I B J I' B' J' s q) (k i : ℕ) : ℝ :=
  max |TransportedPaired.numeric P.legacy k i|
    (max |PreRun.numeric P.firstResource k i| |PreRun.numeric P.secondResource k i|)

def postnumeric (P : Choice hG I B J I' B' J' s q)
    (lengths : ℕ → ℕ) (k i : ℕ) : ℝ :=
  max |TransportedPaired.postnumeric P.legacy lengths k i|
    (max |PreRun.postnumeric P.firstResource lengths k i|
      |PreRun.postnumeric P.secondResource lengths k i|)

/-- The exact selected pre-Run payload remains available beside its physical receipt. -/
structure Receipt (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k)) (R : Run G) where
  sheet : Sheet G
  quote : MapPrices
  chosen : Choice hG I B J I' B' J' sheet quote
  n : ℕ → ℕ
  base_le : sheet.floorL ≤ n
  extra_le : extra chosen ≤ n
  sheet_eq : R.metals.p = ThroughLaunch.raise sheet n
  quote_eq : R.metals.K = ThroughLaunch.raging sheet quote
  numeric_paid : NativeDiagonalClockRequest.PaidRequests
    (numeric chosen) R.family.path.levels
  post_paid : NativeDiagonalClockRequest.PaidRequests
    (postnumeric chosen (fun i => (R.family.path.levels.clock.factor i).val))
    R.family.path.levels
  post_stage : NativePostLengthPayment.StagePaid
    (postnumeric chosen (fun i => (R.family.path.levels.clock.factor i).val) 0)
    R.family.path.levels

private theorem paid_mono {F K : ℕ → ℕ → ℝ} {A : Levels G}
    (h : ∀ k i, |F k i| ≤ |K k i|)
    (hK : NativeDiagonalClockRequest.PaidRequests K A) :
    NativeDiagonalClockRequest.PaidRequests F A := by
  refine ⟨hK.1, ?_⟩
  intro k
  obtain ⟨first, hf⟩ := hK.2 k
  exact ⟨first, fun m hm i hi => (h k i).trans (hf m hm i hi)⟩

variable {R : Run G}

/-- Restrict only the paid requests; the chosen physical sheet and Run stay fixed. -/
def Receipt.project {K : ℕ → Type}
    [∀ k, DecidableEq (K k)] [∀ k, Fintype (K k)]
    {C : ∀ k, Census (K k)} {Q : ∀ k, Request (K k)}
    (r : Receipt hG I B J I' B' J' R)
    (P : PreRun.FamilyChoice hG K C Q r.sheet r.quote)
    (he : ∀ i, PreRun.extra P i ≤ extra r.chosen i)
    (hn : ∀ k i, |PreRun.numeric P k i| ≤ numeric r.chosen k i)
    (hp : ∀ lengths k i, |PreRun.postnumeric P lengths k i| ≤
      postnumeric r.chosen lengths k i) : PreRun.Receipt hG K C Q R :=
  ⟨r.sheet, r.quote, P, r.n, r.base_le, fun i => (he i).trans (r.extra_le i),
    r.sheet_eq, r.quote_eq,
    paid_mono (fun k i => (hn k i).trans (le_abs_self _)) r.numeric_paid,
    paid_mono (fun k i => (hp _ k i).trans (le_abs_self _)) r.post_paid,
    fun m => ((le_abs_self _).trans (hp _ 0 _)).trans (r.post_stage m)⟩

def Receipt.first (r : Receipt hG I B J I' B' J' R) :
    PreRun.Receipt hG (Alphabet I) (fun i => B (seed i))
      (chainRequests r.chosen.first) R :=
  r.project r.chosen.firstResource
    (fun _ => (le_max_left _ _).trans (le_max_right _ _))
    (fun _ _ => (le_max_left _ _).trans (le_max_right _ _))
    (fun _ _ _ => (le_max_left _ _).trans (le_max_right _ _))

def Receipt.second (r : Receipt hG I B J I' B' J' R) :
    PreRun.Receipt hG (Alphabet I') (fun i => B' (seed i))
      (chainRequests r.chosen.second) R :=
  r.project r.chosen.secondResource
    (fun _ => (le_max_right _ _).trans (le_max_right _ _))
    (fun _ _ => (le_max_right _ _).trans (le_max_right _ _))
    (fun _ _ _ => (le_max_right _ _).trans (le_max_right _ _))

def Receipt.leftLegacy (r : Receipt hG I B J I' B' J' R) :
    PreRun.Receipt hG I B J R :=
  r.project r.chosen.legacy.left.resource
    (fun _ => (le_max_left _ _).trans (le_max_left _ _))
    (fun _ _ => ((le_max_left _ _).trans (le_abs_self _)).trans (le_max_left _ _))
    (fun _ _ _ => ((le_max_left _ _).trans (le_abs_self _)).trans (le_max_left _ _))

def Receipt.rightLegacy (r : Receipt hG I B J I' B' J' R) :
    PreRun.Receipt hG I' B' J' R :=
  r.project r.chosen.legacy.right.resource
    (fun _ => (le_max_right _ _).trans (le_max_left _ _))
    (fun _ _ => ((le_max_right _ _).trans (le_abs_self _)).trans (le_max_left _ _))
    (fun _ _ _ => ((le_max_right _ _).trans (le_abs_self _)).trans (le_max_left _ _))

/-- Literal old receipt projections, without an independent receipt choice. -/
def Receipt.legacy (r : Receipt hG I B J I' B' J' R) :
    TransportedPaired.Receipt hG I B J I' B' J' R where
  left := r.leftLegacy
  right := r.rightLegacy
  left_transported := Transported.Attachment.of_entries r.leftLegacy
    r.chosen.legacy.left.entry r.chosen.legacy.left.entry_eq
  right_transported := Transported.Attachment.of_entries r.rightLegacy
    r.chosen.legacy.right.entry r.chosen.legacy.right.entry_eq
  same_sheet := rfl
  same_quote := rfl
  same_n := rfl
  same_native := HEq.rfl

theorem Receipt.native_projections (r : Receipt hG I B J I' B' J' R) :
    r.first.chosen.native = r.chosen.legacy.native ∧
    r.second.chosen.native = r.chosen.legacy.native ∧
    r.legacy.left.chosen.native = r.chosen.legacy.native ∧
    r.legacy.right.chosen.native = r.chosen.legacy.native :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Retain the actual initial payload, rather than choosing another Run or receipt. -/
theorem receipt_of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (Choice hG I B J I' B' J')
      (fun _ _ P => extra P) (fun _ _ P => numeric P)
      (fun _ _ P => postnumeric P) R) :
    Nonempty (Receipt hG I B J I' B' J' R) := by
  rcases h with ⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩
  exact ⟨⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩⟩

/-- Choose one rich grant; its canonical model and raw rate are direct projections. -/
def Receipt.first_grant (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (i : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Profile.Chain.Grant (r.chosen.first (seed i)) (degree i) (depth i)
      R hReadout (PreRun.width_payment r.first i) r.n cap hcap hcap0 :=
  Classical.choice (((r.chosen.first (seed i)).data (degree i) (depth i)).grant
    r.n r.base_le R r.sheet_eq r.quote_eq (PreRun.component r.first) hReadout
    (PreRun.width_payment r.first i) (PreRun.pre_paid r.first i)
    (PreRun.post_request_paid r.first i) cap hcap hcap0)

/-- Choose one rich grant; its canonical model and raw rate are direct projections. -/
def Receipt.second_grant (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (i : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Profile.Chain.Grant (r.chosen.second (seed i)) (degree i) (depth i)
      R hReadout (PreRun.width_payment r.second i) r.n cap hcap hcap0 :=
  Classical.choice (((r.chosen.second (seed i)).data (degree i) (depth i)).grant
    r.n r.base_le R r.sheet_eq r.quote_eq (PreRun.component r.second) hReadout
    (PreRun.width_payment r.second i) (PreRun.pre_paid r.second i)
    (PreRun.post_request_paid r.second i) cap hcap hcap0)


/-- Decode the finite chain index while transporting its payment and rich Grant together. -/
def Receipt.first_at (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Σ P : WidthPayment R.family ((r.chosen.first k).allocation a n).input,
      Profile.Chain.Grant (r.chosen.first k) a n R hReadout P r.n cap hcap hcap0 := by
  have h :
      Σ P : WidthPayment R.family
        ((r.chosen.first (seed (index k a n))).allocation
          (degree (index k a n)) (depth (index k a n))).input,
        Profile.Chain.Grant (r.chosen.first (seed (index k a n)))
          (degree (index k a n)) (depth (index k a n))
          R hReadout P r.n cap hcap hcap0 :=
    ⟨PreRun.width_payment r.first (index k a n),
      r.first_grant hReadout (index k a n) cap hcap hcap0⟩
  obtain ⟨hs,hd,hn⟩ := index_spec k a n
  let grant (k' a' n' : ℕ) :=
    Σ P : WidthPayment R.family ((r.chosen.first k').allocation a' n').input,
      Profile.Chain.Grant (r.chosen.first k') a' n' R hReadout P r.n cap hcap hcap0
  have e : grant (seed (index k a n)) (degree (index k a n)) (depth (index k a n)) =
      grant k a n := by rw [hs,hd,hn]
  exact e.mp h

/-- The actual successor schedule uses precisely the preceding prescribed output width. -/
theorem Receipt.first_successor_width (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    ((r.chosen.first k).allocation a n).target R.family (m + 1) =
      (ActualRequestNumericSchedule.selected R hG hReadout
        ((r.chosen.first k).allocation a (n + 1)).input
        (r.first_at hReadout k a (n + 1) cap hcap hcap0).1
        ((r.chosen.first k).stage a (n + 1)).request
        cap hcap hcap0).inputWidth m :=
  (r.chosen.first k).successor_width a n R hReadout
    (r.first_at hReadout k a (n + 1) cap hcap hcap0).1 cap hcap hcap0 m

/-- Decode the finite chain index while transporting its payment and rich Grant together. -/
def Receipt.second_at (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Σ P : WidthPayment R.family ((r.chosen.second k).allocation a n).input,
      Profile.Chain.Grant (r.chosen.second k) a n R hReadout P r.n cap hcap hcap0 := by
  have h :
      Σ P : WidthPayment R.family
        ((r.chosen.second (seed (index k a n))).allocation
          (degree (index k a n)) (depth (index k a n))).input,
        Profile.Chain.Grant (r.chosen.second (seed (index k a n)))
          (degree (index k a n)) (depth (index k a n))
          R hReadout P r.n cap hcap hcap0 :=
    ⟨PreRun.width_payment r.second (index k a n),
      r.second_grant hReadout (index k a n) cap hcap hcap0⟩
  obtain ⟨hs,hd,hn⟩ := index_spec k a n
  let grant (k' a' n' : ℕ) :=
    Σ P : WidthPayment R.family ((r.chosen.second k').allocation a' n').input,
      Profile.Chain.Grant (r.chosen.second k') a' n' R hReadout P r.n cap hcap hcap0
  have e : grant (seed (index k a n)) (degree (index k a n)) (depth (index k a n)) =
      grant k a n := by rw [hs,hd,hn]
  exact e.mp h

/-- The actual successor schedule uses precisely the preceding prescribed output width. -/
theorem Receipt.second_successor_width (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    ((r.chosen.second k).allocation a n).target R.family (m + 1) =
      (ActualRequestNumericSchedule.selected R hG hReadout
        ((r.chosen.second k).allocation a (n + 1)).input
        (r.second_at hReadout k a (n + 1) cap hcap hcap0).1
        ((r.chosen.second k).stage a (n + 1)).request
        cap hcap hcap0).inputWidth m :=
  (r.chosen.second k).successor_width a n R hReadout
    (r.second_at hReadout k a (n + 1) cap hcap hcap0).1 cap hcap hcap0 m

end YM.Integration.FullQLocal.PreRun.ProfilePaired
end
