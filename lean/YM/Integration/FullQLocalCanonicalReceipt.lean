import YM.Integration.FullQLocalCanonicalPreRun
import YM.Integration.FullQLocalPreRunPurchase

/-!
Transport a retained complete qlocal payload through the same original Run.
An Attachment is indexed by an existing ordinary Receipt. It changes none of
that receipt's resources, physical family, selected widths or floor payments.
The rich-preselection projection below retains the exact chosen resource
payload. It does not upgrade an arbitrary ordinary receipt, and it does not
invoke the Run constructor again.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Complete
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open LocalComparison
open scoped Topology

variable {G : Gauge}

section One
variable {V : Type} [DecidableEq V] [Fintype V]
variable {hG : G.Simple} {B : Census V} {J : Request V}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

/-- The complete conclusion at the exact finite resources already retained. -/
def CompleteAt (D : PreRun.Data hG B J s q native) : Prop :=
  ∀ (n : ℕ → ℕ) (_hbase : s.floorL ≤ n)
    (R : Run G)
    (_hsheet : R.metals.p = ThroughLaunch.raise s n)
    (_hquote : R.metals.K = ThroughLaunch.raging s q)
    (_hNative : NativeComponentRecipe.Realized s q native
      R.family.path.levels R.alloy.B.M)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family D.widths)
    (_hpre : PaidProfile D.preRequest R.family.path.levels)
    (_hpost : PaidProfile
      (D.postRequest (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)),
    Nonempty (Numeric.Canonical.CompleteGrant (Gamma := B) D.capacities (RunFormalChain.fromRun R) J
      (ActualRequestNumericSchedule.selected R hG hReadout D.widths P J cap hcap hcap0)
      D.floor n D.constant)

/-- A complete entry supplies this continuation at its literal projection. -/
theorem Data.complete_at (D : Data hG B J s q native) :
    CompleteAt D.forget :=
  D.grant
end One

/-- Retain the richer conclusion beside the exact ordinary resource payload. -/
structure FamilyChoice (hG : G.Simple) (I : ℕ → Type)
    [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (s : Sheet G) (q : MapPrices) where
  resource : PreRun.FamilyChoice hG I B J s q
  entry k : Data hG (B k) (J k) s q resource.native
  entry_eq k : (entry k).forget = resource.entry k

/-- Select the complete payload once, before its resource projection is used. -/
theorem family_available (H : ManuscriptApplication G) (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (s : Sheet G) (q : MapPrices) :
    Nonempty (FamilyChoice hG I B J s q) := by
  let native := Classical.choice (NativeComponentRecipe.available hG s)
  let entries : ∀ k, Data hG (B k) (J k) s q native :=
    fun k => chooseData H hG (B k) (J k) s q native
  let resource : PreRun.FamilyChoice hG I B J s q :=
    ⟨native, fun k => (entries k).forget⟩
  exact ⟨⟨resource, entries, fun _ => rfl⟩⟩

variable {hG : G.Simple} {I : ℕ → Type}
  [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {s : Sheet G} {q : MapPrices} {R : Run G}

/-- Additional proof data on an existing receipt; there is no new Run field. -/
structure Attachment (r : PreRun.Receipt hG I B J R) : Prop where
  complete k : CompleteAt (r.chosen.entry k)

/-- The projection equality is explicit, rather than an equality of choices. -/
theorem Attachment.of_entries (r : PreRun.Receipt hG I B J R)
    (entries : ∀ k, Data hG (B k) (J k) r.sheet r.quote r.chosen.native)
    (heq : ∀ k, (entries k).forget = r.chosen.entry k) :
    Attachment r := by
  constructor
  intro k
  rw [← heq k]
  exact Data.complete_at (entries k)

/-- Package the same selected resources and the same physical equalities. -/
def receipt (P : FamilyChoice hG I B J s q)
    (n : ℕ → ℕ) (hb : s.floorL ≤ n) (he : PreRun.extra P.resource ≤ n)
    (hs : R.metals.p = ThroughLaunch.raise s n)
    (hq : R.metals.K = ThroughLaunch.raging s q)
    (hn : NativeDiagonalClockRequest.PaidRequests
      (PreRun.numeric P.resource) R.family.path.levels)
    (hp : NativeDiagonalClockRequest.PaidRequests
      (PreRun.postnumeric P.resource
        (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels)
    (ht : NativePostLengthPayment.StagePaid
      (PreRun.postnumeric P.resource
        (fun i => (R.family.path.levels.clock.factor i).val) 0) R.family.path.levels) :
    PreRun.Receipt hG I B J R :=
  ⟨s, q, P.resource, n, hb, he, hs, hq, hn, hp, ht⟩

/-- A rich preselection projects on the identical R, without rerunning choice. -/
theorem receipt_of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (FamilyChoice hG I B J)
      (fun _ _ P => PreRun.extra P.resource)
      (fun _ _ P => PreRun.numeric P.resource)
      (fun _ _ P => PreRun.postnumeric P.resource) R) :
    ∃ r : PreRun.Receipt hG I B J R, Attachment r := by
  rcases h with ⟨s, q, P, n, hb, he, hs, hq, hn, hp, ht⟩
  let r := receipt P n hb he hs hq hn hp ht
  exact ⟨r, Attachment.of_entries r P.entry P.entry_eq⟩

/-- Invoke the complete continuation at the existing receipt's exact schedule,
capacities, constants and original physical Run. No old selected model or
independently chosen Grant is identified with this complete witness. -/
def Attachment.grant {r : PreRun.Receipt hG I B J R} (a : Attachment r)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (k : ℕ) (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Numeric.Canonical.CompleteGrant (Gamma := B k)
      (r.chosen.entry k).capacities (RunFormalChain.fromRun R) (J k)
      (ActualRequestNumericSchedule.selected R hG hReadout
        (r.chosen.entry k).widths (PreRun.width_payment r k) (J k) cap hcap hcap0)
      (r.chosen.entry k).floor r.n (r.chosen.entry k).constant :=
  Classical.choice (a.complete k r.n r.base_le R r.sheet_eq r.quote_eq
    (PreRun.component r) hReadout (PreRun.width_payment r k)
    (PreRun.pre_paid r k) (PreRun.post_request_paid r k) cap hcap hcap0)

end YM.Integration.FullQLocal.PreRun.Complete
end
