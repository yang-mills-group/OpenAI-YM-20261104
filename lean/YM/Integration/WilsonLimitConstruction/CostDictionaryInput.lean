import YM.Integration.FullQLocalCostPairedPreRun
import YM.Integration.ActualOriginalQCountableRequests
import YM.Integration.FullQLocalRequestRegularity

/-!
Exact input record and consumer API extracted from the reviewed
CommonConstructionCostQDictionary revision 3. The unused legacy projection
and broad Run-existence theorem are deliberately outside this module.
CostDictionarySupply remains an explicit mathematical input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CommonConstruction
open Filter Function Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open scoped Classical Topology

/-- Both legacy families and every successive request chain share this one receipt. -/
structure CostDictionarySupply {G : Gauge} (hG : G.Simple)
    (P : ActualQlocalRequestFamily.Recipe) (R : Run G) where
  purchase : FullQLocal.PreRun.CostPaired.Receipt hG
    (ActualOriginalQCountableRequests.Alphabet
      (ActualOriginalQCountableRequests.dictionaryAlphabet P))
    (ActualOriginalQCountableRequests.census
      (A := ActualOriginalQCountableRequests.dictionaryAlphabet P))
    (ActualOriginalQCountableRequests.requests
      (ActualOriginalQCountableRequests.dictionaryBase P))
    (ActualOriginalQCountableRequests.Alphabet
      (ActualOriginalQCountableRequests.dictionaryAlphabet
        (FullQLocalRequestRegularity.closeRecipe P)))
    (ActualOriginalQCountableRequests.census
      (A := ActualOriginalQCountableRequests.dictionaryAlphabet
        (FullQLocalRequestRegularity.closeRecipe P)))
    (ActualOriginalQCountableRequests.requests
      (ActualOriginalQCountableRequests.dictionaryBase
        (FullQLocalRequestRegularity.closeRecipe P))) R
  readout : RG05Preconstruction.ReadoutPurchase R.b


namespace CostDictionarySupply
open Marker FullQLocal FullQLocal.RenderedStep

variable {G : Gauge} {hG : G.Simple} {P : ActualQlocalRequestFamily.Recipe}
  {R : Run G}

private theorem cost_recipe_value {V : Type} {C : Family G}
    {J : FullQLocal.RenderedStep.Request V}
    (e : FullQLocal.PreRun.CostProfile.Recipe) (A : NumericSchedule C J)
    (hsub : e.Subpower A) (m : ℕ) :
    (e.schedule A hsub).admittedCost m = e.cost A m :=
  congrFun (e.schedule_data A hsub).2.2.2.2.2.2.2 m

def original_chain (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) :=
  S.purchase.chosen.first (ActualOriginalQCountableRequests.index j u)

def original_at (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    FullQLocal.PreRun.CostProfile.Chain.Selected (S.original_chain j u) a n
      R S.readout S.purchase.n cap hcap hcap0 :=
  S.purchase.first_at S.readout (ActualOriginalQCountableRequests.index j u)
    a n cap hcap hcap0

/-- This is the exact enlarged schedule occurring in the selected Grant. -/
def original_schedule (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    NumericSchedule R.family ((S.original_chain j u).stage a n).request :=
  ((S.original_chain j u).recipe a n).schedule
    (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.original_chain j u).allocation a n).input (S.original_at j u a n cap hcap hcap0).payment
          ((S.original_chain j u).stage a n).request cap hcap hcap0) (S.original_at j u a n cap hcap hcap0).subpower

theorem original_initial (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a : ℕ) :
    ((S.original_chain j u).stage a 0).request =
      ActualOriginalQPointSetup.request R
        (ActualOriginalQCountableRequests.load j u)
        (ActualOriginalQCountableRequests.base
          (ActualOriginalQCountableRequests.dictionaryBase P)
          (ActualOriginalQCountableRequests.index j u)) :=
by
  let A := ActualOriginalQCountableRequests.dictionaryAlphabet P
  let k := ActualOriginalQCountableRequests.index (A:=A) (D:=D) j u
  let l := ActualOriginalQCountableRequests.load (A:=A) (D:=D) j u
  let b := ActualOriginalQCountableRequests.base (ActualOriginalQCountableRequests.dictionaryBase P) k
  have hq := (ActualOriginalQCountableRequests.covered (A:=A) (D:=D)
    (ActualOriginalQCountableRequests.dictionaryBase P) j u).request
  have hr := (ActualOriginalQPreRunRequest.request_eq (B:=D) l R b).symm
  exact ((S.original_chain j u).initial a).trans (hq.trans hr)


theorem original_capacities (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ) :
    ((S.original_chain j u).stage a n).selected.capacities.vacuumRank ≤
      ((S.original_chain j u).stage a (n + 1)).request.vacuumRankCap ∧
    ((S.original_chain j u).stage a n).selected.capacities.packetRank ≤
      ((S.original_chain j u).stage a (n + 1)).request.inputPacketRankCap ∧
    ((S.original_chain j u).stage a n).selected.capacities.packetPower ≤
      ((S.original_chain j u).stage a (n + 1)).request.inputPacketPowerCap ∧
    a + 2 ≤ ((S.original_chain j u).stage a (n + 1)).request.inputPacketPowerCap :=
  (S.original_chain j u).capacities a n

/-- The next request is exactly the three-cap update of this selected stage. -/
theorem original_successor_request (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ) :
    ((S.original_chain j u).stage a (n + 1)).request =
      FullQLocal.PreRun.SuccessiveRequests.nextRequest
        ((S.original_chain j u).stage a n).request
        ((S.original_chain j u).stage a n).selected.capacities a :=
  (S.original_chain j u).successor_request a n


/-- The complete next cost contains the previous selected cost and one extra power. -/
theorem original_next_cost (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (S.original_schedule j u a (n + 1) cap hcap hcap0).admittedCost m =
      (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.original_chain j u).allocation a (n + 1)).input (S.original_at j u a (n + 1) cap hcap hcap0).payment
          ((S.original_chain j u).stage a (n + 1)).request cap hcap hcap0).admittedCost m +
        (4 : ℝ) ^ ((S.original_chain j u).stage a n).request.order *
          (1 + (S.original_schedule j u a n cap hcap hcap0).admittedCost (m + 1)) ^
            (((S.original_chain j u).data a n).purchases.constant.degree + 1) := by
  simp only [original_schedule, cost_recipe_value]
  exact (S.original_chain j u).next_cost a n R.family
    (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.original_chain j u).allocation a n).input (S.original_at j u a n cap hcap hcap0).payment
          ((S.original_chain j u).stage a n).request cap hcap hcap0) (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.original_chain j u).allocation a (n + 1)).input (S.original_at j u a (n + 1) cap hcap hcap0).payment
          ((S.original_chain j u).stage a (n + 1)).request cap hcap hcap0) (fun _ => rfl) m

theorem original_successor_width (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    ((S.original_chain j u).allocation a n).target R.family (m + 1) =
      (S.original_schedule j u a (n + 1) cap hcap hcap0).inputWidth m :=
  S.purchase.first_successor_width S.readout (ActualOriginalQCountableRequests.index j u)
    a n cap hcap hcap0 m

theorem original_floors_eventually (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ) :
    ∃ first : ℕ, ∀ m, first ≤ m →
      ((S.original_chain j u).data a n).purchases.floor ((S.original_chain j u).stage a n).request S.purchase.sheet
        (R.family.path.levels.clock.J m) ≤ S.purchase.n (R.family.path.levels.clock.J m) ∧
      ((S.original_chain j u).data a n).purchases.floor ((S.original_chain j u).stage a n).request S.purchase.sheet
        (R.family.path.levels.clock.J (m + 1)) ≤ S.purchase.n (R.family.path.levels.clock.J (m + 1)) :=
  S.purchase.first_floors_eventually (ActualOriginalQCountableRequests.index j u) a n

theorem original_local_floors (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet P j →
      MS.Rake.Label D) (a n : ℕ) :
    ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family
      (ActualOriginalQCountableRequests.census
        (A := ActualOriginalQCountableRequests.dictionaryAlphabet P)
        (ActualOriginalQCountableRequests.index j u)), first ≤ d.level →
      FullQLocal.Handoff.LocalFloors
        (((S.original_chain j u).data a n).purchases.floor
          ((S.original_chain j u).stage a n).request S.purchase.sheet) S.purchase.n d := by
  obtain ⟨first, hf⟩ := S.original_floors_eventually j u a n
  exact ⟨first, fun d hd => hf d.level hd⟩


def closed_chain (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) :=
  S.purchase.chosen.second (ActualOriginalQCountableRequests.index j u)

def closed_at (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    FullQLocal.PreRun.CostProfile.Chain.Selected (S.closed_chain j u) a n
      R S.readout S.purchase.n cap hcap hcap0 :=
  S.purchase.second_at S.readout (ActualOriginalQCountableRequests.index j u)
    a n cap hcap hcap0

/-- This is the exact enlarged schedule occurring in the selected Grant. -/
def closed_schedule (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    NumericSchedule R.family ((S.closed_chain j u).stage a n).request :=
  ((S.closed_chain j u).recipe a n).schedule
    (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.closed_chain j u).allocation a n).input (S.closed_at j u a n cap hcap hcap0).payment
          ((S.closed_chain j u).stage a n).request cap hcap hcap0) (S.closed_at j u a n cap hcap hcap0).subpower

theorem closed_initial (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a : ℕ) :
    ((S.closed_chain j u).stage a 0).request =
      ActualOriginalQPointSetup.request R
        (ActualOriginalQCountableRequests.load j u)
        (ActualOriginalQCountableRequests.base
          (ActualOriginalQCountableRequests.dictionaryBase (FullQLocalRequestRegularity.closeRecipe P))
          (ActualOriginalQCountableRequests.index j u)) :=
by
  let A := ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P)
  let k := ActualOriginalQCountableRequests.index (A:=A) (D:=D) j u
  let l := ActualOriginalQCountableRequests.load (A:=A) (D:=D) j u
  let b := ActualOriginalQCountableRequests.base (ActualOriginalQCountableRequests.dictionaryBase (FullQLocalRequestRegularity.closeRecipe P)) k
  have hq := (ActualOriginalQCountableRequests.covered (A:=A) (D:=D)
    (ActualOriginalQCountableRequests.dictionaryBase (FullQLocalRequestRegularity.closeRecipe P)) j u).request
  have hr := (ActualOriginalQPreRunRequest.request_eq (B:=D) l R b).symm
  exact ((S.closed_chain j u).initial a).trans (hq.trans hr)


theorem closed_capacities (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ) :
    ((S.closed_chain j u).stage a n).selected.capacities.vacuumRank ≤
      ((S.closed_chain j u).stage a (n + 1)).request.vacuumRankCap ∧
    ((S.closed_chain j u).stage a n).selected.capacities.packetRank ≤
      ((S.closed_chain j u).stage a (n + 1)).request.inputPacketRankCap ∧
    ((S.closed_chain j u).stage a n).selected.capacities.packetPower ≤
      ((S.closed_chain j u).stage a (n + 1)).request.inputPacketPowerCap ∧
    a + 2 ≤ ((S.closed_chain j u).stage a (n + 1)).request.inputPacketPowerCap :=
  (S.closed_chain j u).capacities a n

/-- The next request is exactly the three-cap update of this selected stage. -/
theorem closed_successor_request (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ) :
    ((S.closed_chain j u).stage a (n + 1)).request =
      FullQLocal.PreRun.SuccessiveRequests.nextRequest
        ((S.closed_chain j u).stage a n).request
        ((S.closed_chain j u).stage a n).selected.capacities a :=
  (S.closed_chain j u).successor_request a n


/-- The complete next cost contains the previous selected cost and one extra power. -/
theorem closed_next_cost (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (S.closed_schedule j u a (n + 1) cap hcap hcap0).admittedCost m =
      (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.closed_chain j u).allocation a (n + 1)).input (S.closed_at j u a (n + 1) cap hcap hcap0).payment
          ((S.closed_chain j u).stage a (n + 1)).request cap hcap hcap0).admittedCost m +
        (4 : ℝ) ^ ((S.closed_chain j u).stage a n).request.order *
          (1 + (S.closed_schedule j u a n cap hcap hcap0).admittedCost (m + 1)) ^
            (((S.closed_chain j u).data a n).purchases.constant.degree + 1) := by
  simp only [closed_schedule, cost_recipe_value]
  exact (S.closed_chain j u).next_cost a n R.family
    (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.closed_chain j u).allocation a n).input (S.closed_at j u a n cap hcap hcap0).payment
          ((S.closed_chain j u).stage a n).request cap hcap hcap0) (ActualRequestNumericSchedule.selected R hG S.readout
          ((S.closed_chain j u).allocation a (n + 1)).input (S.closed_at j u a (n + 1) cap hcap hcap0).payment
          ((S.closed_chain j u).stage a (n + 1)).request cap hcap hcap0) (fun _ => rfl) m

theorem closed_successor_width (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    ((S.closed_chain j u).allocation a n).target R.family (m + 1) =
      (S.closed_schedule j u a (n + 1) cap hcap hcap0).inputWidth m :=
  S.purchase.second_successor_width S.readout (ActualOriginalQCountableRequests.index j u)
    a n cap hcap hcap0 m

theorem closed_floors_eventually (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ) :
    ∃ first : ℕ, ∀ m, first ≤ m →
      ((S.closed_chain j u).data a n).purchases.floor ((S.closed_chain j u).stage a n).request S.purchase.sheet
        (R.family.path.levels.clock.J m) ≤ S.purchase.n (R.family.path.levels.clock.J m) ∧
      ((S.closed_chain j u).data a n).purchases.floor ((S.closed_chain j u).stage a n).request S.purchase.sheet
        (R.family.path.levels.clock.J (m + 1)) ≤ S.purchase.n (R.family.path.levels.clock.J (m + 1)) :=
  S.purchase.second_floors_eventually (ActualOriginalQCountableRequests.index j u) a n

theorem closed_local_floors (S : CostDictionarySupply hG P R) {D : MS.Local.Physical.Deck G}
    (j : ℕ) (u : ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P) j →
      MS.Rake.Label D) (a n : ℕ) :
    ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family
      (ActualOriginalQCountableRequests.census
        (A := ActualOriginalQCountableRequests.dictionaryAlphabet (FullQLocalRequestRegularity.closeRecipe P))
        (ActualOriginalQCountableRequests.index j u)), first ≤ d.level →
      FullQLocal.Handoff.LocalFloors
        (((S.closed_chain j u).data a n).purchases.floor
          ((S.closed_chain j u).stage a n).request S.purchase.sheet) S.purchase.n d := by
  obtain ⟨first, hf⟩ := S.closed_floors_eventually j u a n
  exact ⟨first, fun d hd => hf d.level hd⟩


end CostDictionarySupply

end YM.Integration.CommonConstruction
end
