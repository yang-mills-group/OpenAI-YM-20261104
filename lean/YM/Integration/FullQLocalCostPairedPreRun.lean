import YM.Integration.FullQLocalCostProfileResources
import YM.Integration.FullQLocalCostChainReceipts
import YM.Integration.FullQLocalProfilePairedPreRun

/-!
Retain both legacy families and both successive cost-profile families before
the sole Run choice. New resources are purchased directly, without treating
enlarged-cost data as an old analytic Grant.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostPaired
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open CostProfile
open scoped Topology

variable {G : Gauge} {hG : G.Simple}
  {I : ℕ → Type} [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

def chainResource (C : ∀ k, CostProfile.Chain hG (B k) (J k) s q native)
    (i : ℕ) : Resources :=
  ((C (ProfilePaired.seed i)).data (ProfilePaired.degree i)
    (ProfilePaired.depth i)).resources

private theorem chainResource_index (C : ∀ k, CostProfile.Chain hG (B k) (J k) s q native)
    (k a n : ℕ) : chainResource C (ProfilePaired.index k a n) = ((C k).data a n).resources := by
  obtain ⟨hs,hd,hn⟩ := ProfilePaired.index_spec k a n
  let resource (k' a' n' : ℕ) : Resources := ((C k').data a' n').resources
  change resource (ProfilePaired.seed _) (ProfilePaired.degree _) (ProfilePaired.depth _) = resource k a n
  rw [hs,hd,hn]

structure Choice (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) where
  legacy : ProfilePaired.Choice hG I B J I' B' J' s q
  first k : CostProfile.Chain hG (B k) (J k) s q legacy.legacy.native
  second k : CostProfile.Chain hG (B' k) (J' k) s q legacy.legacy.native

variable {I' : ℕ → Type} [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
  {B' : ∀ k, Census (I' k)} {J' : ∀ k, Request (I' k)}

def Choice.firstResource (P : Choice hG I B J I' B' J' s q) : ℕ → Resources :=
  chainResource P.first

def Choice.secondResource (P : Choice hG I B J I' B' J' s q) : ℕ → Resources :=
  chainResource P.second

theorem available (H : CostProfile.ManuscriptApplication G) (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) :
    Nonempty (Choice hG I B J I' B' J' s q) := by
  let P := Classical.choice (ProfilePaired.available H.profile hG I B J I' B' J' s q)
  exact ⟨⟨P,
    fun k => CostProfile.chooseChain H hG (B k) (J k) s q P.legacy.native,
    fun k => CostProfile.chooseChain H hG (B' k) (J' k) s q P.legacy.native⟩⟩

def extra (P : Choice hG I B J I' B' J' s q) (i : ℕ) : ℕ :=
  max (ProfilePaired.extra P.legacy i)
    (max (Resources.extra s.floorL P.firstResource i)
      (Resources.extra s.floorL P.secondResource i))

def numeric (P : Choice hG I B J I' B' J' s q) (k i : ℕ) : ℝ :=
  max |ProfilePaired.numeric P.legacy k i|
    (max |Resources.numeric P.firstResource k i|
      |Resources.numeric P.secondResource k i|)

def postnumeric (P : Choice hG I B J I' B' J' s q)
    (lengths : ℕ → ℕ) (k i : ℕ) : ℝ :=
  max |ProfilePaired.postnumeric P.legacy lengths k i|
    (max |Resources.postnumeric P.firstResource lengths k i|
      |Resources.postnumeric P.secondResource lengths k i|)

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

def Receipt.legacy (r : Receipt hG I B J I' B' J' R) :
    ProfilePaired.Receipt hG I B J I' B' J' R :=
  ⟨r.sheet, r.quote, r.chosen.legacy, r.n, r.base_le,
    fun i => (le_max_left _ _).trans (r.extra_le i), r.sheet_eq, r.quote_eq,
    paid_mono (fun _ _ => (le_max_left _ _).trans (le_abs_self _)) r.numeric_paid,
    paid_mono (fun _ _ => (le_max_left _ _).trans (le_abs_self _)) r.post_paid,
    fun m => ((le_abs_self _).trans (le_max_left _ _)).trans (r.post_stage m)⟩

theorem Receipt.first (r : Receipt hG I B J I' B' J' R) :
    Resources.Receipt r.chosen.firstResource R r.sheet.floorL r.n where
  extra_le i := ((le_max_left _ _).trans (le_max_right _ _)).trans (r.extra_le i)
  numeric_paid := paid_mono
    (fun _ _ => ((le_max_left _ _).trans (le_max_right _ _)).trans (le_abs_self _))
    r.numeric_paid
  post_paid := paid_mono
    (fun _ _ => ((le_max_left _ _).trans (le_max_right _ _)).trans (le_abs_self _))
    r.post_paid

theorem Receipt.second (r : Receipt hG I B J I' B' J' R) :
    Resources.Receipt r.chosen.secondResource R r.sheet.floorL r.n where
  extra_le i := ((le_max_right _ _).trans (le_max_right _ _)).trans (r.extra_le i)
  numeric_paid := paid_mono
    (fun _ _ => ((le_max_right _ _).trans (le_max_right _ _)).trans (le_abs_self _))
    r.numeric_paid
  post_paid := paid_mono
    (fun _ _ => ((le_max_right _ _).trans (le_max_right _ _)).trans (le_abs_self _))
    r.post_paid

theorem receipt_of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (Choice hG I B J I' B' J') (fun _ _ P => extra P)
      (fun _ _ P => numeric P) (fun _ _ P => postnumeric P) R) :
    Nonempty (Receipt hG I B J I' B' J' R) := by
  rcases h with ⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩
  exact ⟨⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩⟩

def Receipt.first_payment (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    WidthPayment R.family ((r.chosen.first k).allocation a n).input := by
  have P := r.first.width_payment (ProfilePaired.index k a n)
  simpa only [Choice.firstResource, chainResource_index, CostProfile.Data.resources] using P

theorem Receipt.first_pre_paid (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    PaidProfile (((r.chosen.first k).data a n).purchases.pre
      ((r.chosen.first k).stage a n).request ((r.chosen.first k).allocation a n)) R.family.path.levels := by
  have h := r.first.pre_paid (ProfilePaired.index k a n)
  simpa only [Choice.firstResource, chainResource_index, CostProfile.Data.resources] using h

theorem Receipt.first_post_paid (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    PaidProfile (((r.chosen.first k).data a n).purchases.post
      (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels := by
  have h := r.first.post_request_paid (ProfilePaired.index k a n)
  simpa only [Choice.firstResource, chainResource_index, CostProfile.Data.resources] using h

theorem Receipt.first_floors_eventually
    (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    ∃ start : ℕ, ∀ m, start ≤ m →
      ((r.chosen.first k).data a n).purchases.floor ((r.chosen.first k).stage a n).request r.sheet
          (R.family.path.levels.clock.J m) ≤ r.n (R.family.path.levels.clock.J m) ∧
      ((r.chosen.first k).data a n).purchases.floor ((r.chosen.first k).stage a n).request r.sheet
          (R.family.path.levels.clock.J (m + 1)) ≤ r.n (R.family.path.levels.clock.J (m + 1)) := by
  have h := r.first.floors_eventually (ProfilePaired.index k a n)
  simpa only [Choice.firstResource, chainResource_index, CostProfile.Data.resources] using h

def Receipt.first_at (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) :
    CostProfile.Chain.Selected (r.chosen.first k) a n R hReadout r.n cap hcap hcap0 := by
  let P := fun d => r.first_payment k a d
  let hsub := (r.chosen.first k).subpower a R hReadout P cap hcap hcap0 n
  refine ⟨P n, hsub, ?_⟩
  exact Classical.choice (((r.chosen.first k).data a n).grant r.n r.base_le R
    r.sheet_eq r.quote_eq (PreRun.component r.legacy.first) hReadout (P n)
    (r.first_pre_paid k a n) (r.first_post_paid k a n) cap hcap hcap0 hsub)

theorem Receipt.first_successor_width (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0))
    (m : ℕ) :
    ((r.chosen.first k).allocation a n).target R.family (m + 1) =
      (((r.chosen.first k).recipe a (n + 1)).schedule
        (ActualRequestNumericSchedule.selected R hG hReadout
          ((r.chosen.first k).allocation a (n + 1)).input
          (r.first_at hReadout k a (n + 1) cap hcap hcap0).payment
          ((r.chosen.first k).stage a (n + 1)).request cap hcap hcap0)
        (r.first_at hReadout k a (n + 1) cap hcap hcap0).subpower).inputWidth m :=
  (r.chosen.first k).successor_width a n R hReadout
    (r.first_at hReadout k a (n + 1) cap hcap hcap0).payment cap hcap hcap0
    (r.first_at hReadout k a (n + 1) cap hcap hcap0).subpower m

def Receipt.second_payment (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    WidthPayment R.family ((r.chosen.second k).allocation a n).input := by
  have P := r.second.width_payment (ProfilePaired.index k a n)
  simpa only [Choice.secondResource, chainResource_index, CostProfile.Data.resources] using P

theorem Receipt.second_pre_paid (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    PaidProfile (((r.chosen.second k).data a n).purchases.pre
      ((r.chosen.second k).stage a n).request ((r.chosen.second k).allocation a n)) R.family.path.levels := by
  have h := r.second.pre_paid (ProfilePaired.index k a n)
  simpa only [Choice.secondResource, chainResource_index, CostProfile.Data.resources] using h

theorem Receipt.second_post_paid (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    PaidProfile (((r.chosen.second k).data a n).purchases.post
      (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels := by
  have h := r.second.post_request_paid (ProfilePaired.index k a n)
  simpa only [Choice.secondResource, chainResource_index, CostProfile.Data.resources] using h

theorem Receipt.second_floors_eventually
    (r : Receipt hG I B J I' B' J' R) (k a n : ℕ) :
    ∃ start : ℕ, ∀ m, start ≤ m →
      ((r.chosen.second k).data a n).purchases.floor ((r.chosen.second k).stage a n).request r.sheet
          (R.family.path.levels.clock.J m) ≤ r.n (R.family.path.levels.clock.J m) ∧
      ((r.chosen.second k).data a n).purchases.floor ((r.chosen.second k).stage a n).request r.sheet
          (R.family.path.levels.clock.J (m + 1)) ≤ r.n (R.family.path.levels.clock.J (m + 1)) := by
  have h := r.second.floors_eventually (ProfilePaired.index k a n)
  simpa only [Choice.secondResource, chainResource_index, CostProfile.Data.resources] using h

def Receipt.second_at (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) :
    CostProfile.Chain.Selected (r.chosen.second k) a n R hReadout r.n cap hcap hcap0 := by
  let P := fun d => r.second_payment k a d
  let hsub := (r.chosen.second k).subpower a R hReadout P cap hcap hcap0 n
  refine ⟨P n, hsub, ?_⟩
  exact Classical.choice (((r.chosen.second k).data a n).grant r.n r.base_le R
    r.sheet_eq r.quote_eq (PreRun.component r.legacy.first) hReadout (P n)
    (r.second_pre_paid k a n) (r.second_post_paid k a n) cap hcap hcap0 hsub)

theorem Receipt.second_successor_width (r : Receipt hG I B J I' B' J' R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) (k a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0))
    (m : ℕ) :
    ((r.chosen.second k).allocation a n).target R.family (m + 1) =
      (((r.chosen.second k).recipe a (n + 1)).schedule
        (ActualRequestNumericSchedule.selected R hG hReadout
          ((r.chosen.second k).allocation a (n + 1)).input
          (r.second_at hReadout k a (n + 1) cap hcap hcap0).payment
          ((r.chosen.second k).stage a (n + 1)).request cap hcap hcap0)
        (r.second_at hReadout k a (n + 1) cap hcap hcap0).subpower).inputWidth m :=
  (r.chosen.second k).successor_width a n R hReadout
    (r.second_at hReadout k a (n + 1) cap hcap hcap0).payment cap hcap hcap0
    (r.second_at hReadout k a (n + 1) cap hcap hcap0).subpower m

end YM.Integration.FullQLocal.PreRun.CostPaired
end
