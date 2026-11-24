import YM.Integration.WilsonLimitConstruction.CostDictionaryInput
import YM.Integration.WilsonLimitConstruction.CostProfileGrants
import YM.Integration.WilsonLimitConstruction.FundedRetargetAgreement
import YM.Integration.WilsonLimitConstruction.FundedPlateauRun

/-!
The original dictionary and its regularity closure are selected on the native
sheet and quote, before the common block lengths and the Run.  The timing,
campaign and every dictionary entry therefore use one witness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCostDictionary

open Lattice RG RG.Supply Precision Marker FullQLocal
open FullQLocal.RenderedStep (Request)
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open ActualOriginalQCountableRequests FullQLocal.PreRun
open scoped Classical

variable {G : Gauge}

section Chains

variable {V : Type} [DecidableEq V] [Fintype V] {hG : G.Simple}
    {B : Census V} {J : Request V} {s : Sheet G} {q : MapPrices}
    {native : NativeComponentRecipe.Choice s}

/-- Each selected stage already supplies its identity-cost branch at the
original allocation. The legacy chain has the same requests and widths. -/
def profileChain (S : CostProfile.Chain hG B J s q native) :
    Profile.Chain hG B J s q native where
  stage r n := ⟨(S.stage r n).request, (S.stage r n).selected.forget⟩
  initial := S.initial
  capacities := S.capacities
  shape := S.shape
  allocation := S.allocation
  adjacent := S.adjacent
  data r n := by
    cases n with
    | zero => exact CostProfileGrants.keepProfile (S.data r 0) (S.recipe_initial r)
    | succ n =>
        exact ((S.stage r (n + 1)).selected.chooseData (S.allocation r (n + 1)) .keep).forget

theorem profileChain_initial_purchases (S : CostProfile.Chain hG B J s q native) (r : ℕ) :
    ((profileChain S).data r 0).purchases = (S.data r 0).purchases :=
  CostProfileGrants.keepProfile_purchases (S.data r 0) (S.recipe_initial r)

/-- The initial selected specification supplies the original transported seed
for the same census, request, sheet, quote and native component. -/
def transportedSeed (S : CostProfile.Chain hG B J s q native) :
    Transported.Data hG B J s q native :=
  S.initial 0 ▸ (S.stage 0 0).selected.forget.transported

end Chains

/-- Only the two rich chain families on one native choice are needed. -/
structure Chains (hG : G.Simple)
    (I : ℕ → Type) [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
    (B : ∀ k, Census (I k)) (J : ∀ k, Request (I k))
    (I' : ℕ → Type) [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
    (B' : ∀ k, Census (I' k)) (J' : ∀ k, Request (I' k))
    (s : Sheet G) (q : MapPrices) where
  native : NativeComponentRecipe.Choice s
  first k : CostProfile.Chain hG (B k) (J k) s q native
  second k : CostProfile.Chain hG (B' k) (J' k) s q native

section Paired

variable {hG : G.Simple} {s : Sheet G} {q : MapPrices}
  {I : ℕ → Type} [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {I' : ℕ → Type} [∀ k, DecidableEq (I' k)] [∀ k, Fintype (I' k)]
  {B' : ∀ k, Census (I' k)} {J' : ∀ k, Request (I' k)}

def Chains.paired (A : Chains hG I B J I' B' J' s q) :
    CostPaired.Choice hG I B J I' B' J' s q where
  legacy := {
    legacy := {
      native := A.native
      first k := transportedSeed (A.first k)
      second k := transportedSeed (A.second k) }
    first k := profileChain (A.first k)
    second k := profileChain (A.second k) }
  first := A.first
  second := A.second

theorem choice_iff :
    Nonempty (CostPaired.Choice hG I B J I' B' J' s q) ↔
      Nonempty (Chains hG I B J I' B' J' s q) :=
  ⟨fun h => h.map fun A => ⟨A.legacy.legacy.native, A.first, A.second⟩,
    fun h => h.map Chains.paired⟩

end Paired

/-- The concrete family depends only on the requested dictionary and the
preconstruction sheet and quote. -/
abbrev Demand (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (s : Sheet G) (q : MapPrices) :=
  CostPaired.Choice hG
    (Alphabet (dictionaryAlphabet P)) (census (A := dictionaryAlphabet P))
    (requests (dictionaryBase P))
    (Alphabet (dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P)))
    (census (A := dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P)))
    (requests (dictionaryBase (FullQLocalRequestRegularity.closeRecipe P))) s q

abbrev DictionaryChains (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (s : Sheet G) (q : MapPrices) :=
  Chains hG
    (Alphabet (dictionaryAlphabet P)) (census (A := dictionaryAlphabet P))
    (requests (dictionaryBase P))
    (Alphabet (dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P)))
    (census (A := dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P)))
    (requests (dictionaryBase (FullQLocalRequestRegularity.closeRecipe P))) s q

/-- A purchased dictionary in turn exhibits both rich chain families at
its own recorded sheet and quote. -/
theorem chains_of_supply {hG : G.Simple} {P : ActualQlocalRequestFamily.Recipe}
    {R : Run G} (S : CommonConstruction.CostDictionarySupply hG P R) :
    Nonempty (DictionaryChains hG P S.purchase.sheet S.purchase.quote) :=
  choice_iff.mp ⟨S.purchase.chosen⟩

/-- Funding and the analytic application receipts for both literal request
families share the Run selected by the native treasury/period construction. -/
structure Purchase (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) (ε : ℝ) where
  run : Run G
  campaign : Campaign run
  pillars : Campaign.Pillars run campaign
  penalty : run.family.path.levels.clock.kernel.penalty = ε
  funded : R2I.Funded Δ run campaign
  orders (j : ℕ) : j ≤ (run.metals.p.profile j).order ∧
    j ≤ (run.metals.p.profile j).power
  treasury : CalendarTreasuryPurchase.TreasuryFunded run.family.path.levels
  period : CommonPeriodPurchase.Funded run.metals.K run.metals.O run.family.path.levels
  dictionary : CommonConstruction.CostDictionarySupply hG P run

/-- The dictionary, factor prediction and regulator plateaux belong to the
same original funded Run and the same Campaign. -/
structure PredictionPurchase (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) (ε : ℝ) (prediction : FundedCompanySelection.Prediction G) where
  original : Purchase hG P Δ ε
  predicted : prediction original.run.kit
  plateau : NativeFVAPlateau.Funded original.run.family.path.levels

/-- Buy the factor estimate and regulator plateaux in the native construction
that selects the two literal request dictionaries. -/
theorem purchase_with_prediction (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    Nonempty (PredictionPurchase hG P Δ ε (@prediction)) := by
  obtain ⟨native, hPrediction⟩ := FundedPlateauRun.purchase hG Δ hε
    (Demand hG P) available (fun _ _ choice => CostPaired.extra choice)
    (fun _ _ choice => CostPaired.numeric choice)
    (fun _ _ choice => CostPaired.postnumeric choice) (@prediction) paid
  obtain ⟨receipt⟩ := CostPaired.receipt_of_preselection native.run native.selected
  exact ⟨⟨⟨native.run, native.campaign, native.pillars, native.penalty, native.funded,
    native.orders, native.treasury, native.period, ⟨receipt, native.readout⟩⟩,
    hPrediction, native.windows⟩⟩

/-- It suffices to construct these two countable pre-Run choice families.
There is no existential choice of a physical Run in this premise. -/
theorem purchase_of_preselection (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (Demand hG P s q)) :
    Nonempty (Purchase hG P Δ ε) :=
  (purchase_with_prediction hG P Δ hε available (@FundedPredictionSupply.Always G)
    (fun s T => FundedPredictionSupply.always s (PhysicalNext.ThroughLaunch.raging s T))).map
    PredictionPurchase.original

/-- The two actual rich chain families supply every legacy component and
fund the original Run through one postnumeric preselection. -/
theorem purchase_of_chains (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (DictionaryChains hG P s q)) :
    Nonempty (Purchase hG P Δ ε) :=
  purchase_of_preselection hG P Δ hε fun s q => (available s q).map Chains.paired

/-- Specialize the analytic supplier to the requested dictionaries, before
the single physical Run is formed. -/
theorem purchase (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (H : CostProfile.ManuscriptApplication G) (Δ : Decal G)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (Purchase hG P Δ ε) :=
  purchase_of_preselection hG P Δ hε
    (CostPaired.available H hG _ _ _ _ _ _)

/-- The grant-only analytic application suffices for the same funded Run. -/
theorem purchase_of_grants (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (H : CostProfileGrants.Application G) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (Purchase hG P Δ ε) :=
  purchase hG P ((CostProfileGrants.application_iff G).mpr H) Δ hε

variable {hG : G.Simple} {P : ActualQlocalRequestFamily.Recipe}
    {Δ : Decal G} {ε : ℝ}

/-- The native funded dictionary uses exactly the UV provider's selected
quote on the same preliminary sheet and price. -/
theorem Purchase.uv_price (A : Purchase hG P Δ ε) :
    A.run.metals.K = UVExtension.Case.actualPay A.dictionary.purchase.sheet
      A.dictionary.purchase.quote :=
  A.dictionary.purchase.quote_eq.trans (FundedRetargetAgreement.prices _ _)

theorem Purchase.attached (A : Purchase hG P Δ ε) :
    ActualRunNativeComponentRecipe.Attached A.run :=
  FullQLocal.PreRun.attached A.dictionary.purchase.legacy.first

universe u

theorem Purchase.broad (A : Purchase hG P Δ ε) :
    R2IGoals.Broad.{u} Δ A.pillars hG :=
  R2IGoals.fromFunded A.pillars hG A.funded

end YM.Integration.WilsonLimitConstruction.FundedCostDictionary
end
