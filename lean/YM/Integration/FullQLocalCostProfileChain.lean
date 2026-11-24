import YM.Integration.FullQLocalCostRecipe
import YM.Integration.FullQLocalCostProfileSpecification
import YM.Integration.FullQLocalProfileChain

/-!
Select each finite successor cost from the previous data's fixed degree before
the physical Run. Capacities and coherent positive width allocations are chosen
first. Each recipe and its data remain one dependent pair.
The original profile construction is retained through the keep projection.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open Profile
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
variable {hG : G.Simple} {B : Census V} {J : Request V}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

omit [DecidableEq V] [Fintype V] in
/-- The new hypothesis supplies the old interface only by its literal keep branch. -/
theorem ManuscriptApplication.profile (H : ManuscriptApplication G) :
    Profile.ManuscriptApplication G := by
  intro hG V instD instF B J s q native
  exact ⟨(chooseSpecification H hG B J s q native).forget⟩

/-- A specification at every finite depth, retaining the exact preceding choice. -/
def specificationStage (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r : ℕ) :
    ℕ → SuccessiveRequests.Stage (fun K => Specification hG B K s q native) :=
  SuccessiveRequests.Stage.chain (fun K (S : Specification hG B K s q native) => S.capacities)
    (fun K => chooseSpecification H hG B K s q native) r
    ⟨J, chooseSpecification H hG B J s q native⟩

/-- Bound stage n's output by the next specification's external input strip. -/
def stageComponents (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r n : ℕ) :
    ComponentAllocation (specificationStage H hG B J s q native r n).selected.diagram :=
  boundedComponents (specificationStage H hG B J s q native r n).selected.diagram
    (specificationStage H hG B J s q native r (n + 1)).selected.diagram.inputStrip

/-- Every later input is the preceding actual output, with no width restriction step. -/
def stageInput (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r : ℕ) : ℕ → ProfileWidths
  | 0 => (specificationStage H hG B J s q native r 0).selected.diagram.inputStrip
  | n + 1 => (stageComponents H hG B J s q native r n).component
      (specificationStage H hG B J s q native r n).selected.diagram.output

def stageAllocation (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r n : ℕ) :
    Allocation (specificationStage H hG B J s q native r n).selected.diagram where
  input := stageInput H hG B J s q native r n
  component := (stageComponents H hG B J s q native r n).component
  input_strip i := by
    cases n with
    | zero => exact le_rfl
    | succ n =>
        exact boundedComponents_output
          (specificationStage H hG B J s q native r n).selected.diagram
          (specificationStage H hG B J s q native r (n + 1)).selected.diagram.inputStrip i
  component_strip := (stageComponents H hG B J s q native r n).component_strip
  same_mesh := (stageComponents H hG B J s q native r n).same_mesh

theorem stageAllocation_successor (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r n : ℕ) :
    (stageAllocation H hG B J s q native r n).output =
      (stageAllocation H hG B J s q native r (n + 1)).input := rfl

/-- Recipes and their data are selected together, using only the previous
pre-Run degree. No price coefficient or physical Run enters this recursion. -/
def stageData (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) (r : ℕ) :
    (n : ℕ) → Σ e : Recipe, Data hG B
      (specificationStage H hG B J s q native r n).request s q native
      (specificationStage H hG B J s q native r n).selected.capacities
      (specificationStage H hG B J s q native r n).selected.diagram
      (stageAllocation H hG B J s q native r n) e
  | 0 => ⟨.keep, (specificationStage H hG B J s q native r 0).selected.chooseData
      (stageAllocation H hG B J s q native r 0) .keep⟩
  | n + 1 =>
    let previous := stageData H hG B J s q native r n
    let following := previous.1.next (stageAllocation H hG B J s q native r n).input
      previous.2.purchases.constant.degree
      (specificationStage H hG B J s q native r n).request.order
    ⟨following, (specificationStage H hG B J s q native r (n + 1)).selected.chooseData
      (stageAllocation H hG B J s q native r (n + 1)) following⟩

/-- A countable family of fully selected pre-Run data with exact adjacency. -/
structure Chain (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s) where
  stage : ℕ → ℕ → SuccessiveRequests.Stage
    (fun K => Specification hG B K s q native)
  initial r : (stage r 0).request = J
  capacities r n :
    (stage r n).selected.capacities.vacuumRank ≤ (stage r (n + 1)).request.vacuumRankCap ∧
    (stage r n).selected.capacities.packetRank ≤ (stage r (n + 1)).request.inputPacketRankCap ∧
    (stage r n).selected.capacities.packetPower ≤ (stage r (n + 1)).request.inputPacketPowerCap ∧
    r + 2 ≤ (stage r (n + 1)).request.inputPacketPowerCap
  shape r n : SuccessiveRequests.skeleton (stage r n).request =
    SuccessiveRequests.skeleton J
  allocation r n : Allocation (stage r n).selected.diagram
  adjacent r n : (allocation r n).output = (allocation r (n + 1)).input
  selected r n : Σ e : Recipe, Data hG B (stage r n).request s q native
    (stage r n).selected.capacities (stage r n).selected.diagram (allocation r n) e
  initial_recipe r : (selected r 0).1 = .keep
  next_recipe r n : (selected r (n + 1)).1 =
    (selected r n).1.next (allocation r n).input
      (selected r n).2.purchases.constant.degree (stage r n).request.order
  successor_request r n : (stage r (n+1)).request =
    SuccessiveRequests.nextRequest (stage r n).request (stage r n).selected.capacities r

/-- No physical datum or Run occurs in this simultaneous selection. -/
def chooseChain (H : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) : Chain hG B J s q native where
  stage := specificationStage H hG B J s q native
  initial _ := rfl
  capacities r n := SuccessiveRequests.Stage.chain_caps
    (fun K (S : Specification hG B K s q native) => S.capacities) (fun K => chooseSpecification H hG B K s q native) r
    ⟨J, chooseSpecification H hG B J s q native⟩ n
  shape r n := SuccessiveRequests.Stage.chain_skeleton
    (fun K (S : Specification hG B K s q native) => S.capacities) (fun K => chooseSpecification H hG B K s q native) r
    ⟨J, chooseSpecification H hG B J s q native⟩ n
  allocation := stageAllocation H hG B J s q native
  adjacent := stageAllocation_successor H hG B J s q native
  selected := stageData H hG B J s q native
  initial_recipe _ := rfl
  next_recipe _ _ := rfl
  successor_request _ _ := rfl

/-- The finite syntax and selected data remain a dependent pair. -/
def Chain.recipe (S : Chain hG B J s q native) (r n : ℕ) : Recipe :=
  (S.selected r n).1

def Chain.data (S : Chain hG B J s q native) (r n : ℕ) :
    Data hG B (S.stage r n).request s q native
      (S.stage r n).selected.capacities (S.stage r n).selected.diagram
      (S.allocation r n) (S.recipe r n) :=
  (S.selected r n).2

theorem Chain.recipe_initial (S : Chain hG B J s q native) (r : ℕ) :
    S.recipe r 0 = .keep := S.initial_recipe r

theorem Chain.recipe_successor (S : Chain hG B J s q native) (r n : ℕ) :
    S.recipe r (n + 1) =
      (S.recipe r n).next (S.allocation r n).input
        (S.data r n).purchases.constant.degree (S.stage r n).request.order :=
  S.next_recipe r n

/-- The bought successor cost contains the full previous shifted cost.
The coefficient is deliberately absent from this pre-Run identity. -/
theorem Chain.next_cost (S : Chain hG B J s q native) (r n : ℕ)
    (C : Family G)
    (A : NumericSchedule C (S.stage r n).request)
    (A' : NumericSchedule C (S.stage r (n + 1)).request)
    (hbase : ∀ m, 2 * ActualRunComponentAdmission.cost C
      (S.allocation r n).input m = A.admittedCost m) (m : ℕ) :
    (S.recipe r (n + 1)).cost A' m =
      A'.admittedCost m + (4 : ℝ) ^ (S.stage r n).request.order *
        (1 + (S.recipe r n).cost A (m + 1)) ^
          ((S.data r n).purchases.constant.degree + 1) := by
  rw [S.recipe_successor, Recipe.next_cost,
    Recipe.total_eval (S.recipe r n) (S.allocation r n).input A hbase]

/-- Enlarging admitted cost leaves the exact adjacent physical width intact. -/
theorem Chain.successor_width (S : Chain hG B J s q native) (r n : ℕ)
    (R : Run G) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family (S.allocation r (n + 1)).input)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0))
    (hsub : (S.recipe r (n + 1)).Subpower
      (ActualRequestNumericSchedule.selected R hG hReadout
        (S.allocation r (n + 1)).input P (S.stage r (n + 1)).request cap hcap hcap0))
    (m : ℕ) :
    (S.allocation r n).target R.family (m + 1) =
      ((S.recipe r (n + 1)).schedule
        (ActualRequestNumericSchedule.selected R hG hReadout
          (S.allocation r (n + 1)).input P (S.stage r (n + 1)).request cap hcap hcap0)
        hsub).inputWidth m := by
  rw [((S.recipe r (n + 1)).schedule_data
    (ActualRequestNumericSchedule.selected R hG hReadout
      (S.allocation r (n + 1)).input P (S.stage r (n + 1)).request cap hcap hcap0)
    hsub).2.2.1]
  exact Allocation.successor_width (S.allocation r n) (S.allocation r (n + 1)).input
    (S.adjacent r n) R hG hReadout P (S.stage r (n + 1)).request cap hcap hcap0 m

end YM.Integration.FullQLocal.PreRun.CostProfile
end
