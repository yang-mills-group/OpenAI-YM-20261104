import YM.Integration.FullQLocalProfileAllocation
import YM.Integration.FullQLocalSuccessiveRequests

/-!
Construct every finite successor specification and its coherent positive widths
before selecting a physical Run. Each stage's designated output is literally
the following stage's external input. The original transported interface is
also obtained from a diagonal allocation of the same full hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Profile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
variable {hG : G.Simple} {B : Census V} {J : Request V}
  {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

/-- Select a complete finite component allocation once at its prescribed bound. -/
def boundedComponents (D : Diagram s q native) (upper : ProfileWidths) :
    ComponentAllocation D :=
  Classical.choose (components_below D upper)

omit [DecidableEq V] [Fintype V] in
theorem boundedComponents_output (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) :
    ((boundedComponents D upper).component D.output).width i ≤ upper.width i :=
  Classical.choose_spec (components_below D upper) i

/-- Equal external input and designated output recover the old transported width. -/
def diagonalAllocation (D : Diagram s q native) : Allocation D where
  input := (boundedComponents D D.inputStrip).component D.output
  component := (boundedComponents D D.inputStrip).component
  input_strip := boundedComponents_output D D.inputStrip
  component_strip := (boundedComponents D D.inputStrip).component_strip
  same_mesh := (boundedComponents D D.inputStrip).same_mesh

omit [DecidableEq V] [Fintype V] in
theorem diagonalAllocation_output (D : Diagram s q native) :
    (diagonalAllocation D).output = (diagonalAllocation D).input := rfl

/-- Project the exact prescribed grant only when the two profiles are equal. -/
def Data.transported {caps : Handoff.OutputCapacities}
    {D : Diagram s q native} {W : Allocation D}
    (E : Data hG B J s q native caps D W) (hW : W.output = W.input) :
    Transported.Data hG B J s q native where
  widths := W.input
  widths_le i := (W.input_strip i).trans (D.input_native i)
  floor := E.purchases.floor J s
  preRequest := E.purchases.pre J W
  postRequest := E.purchases.post
  capacities := caps
  constant := E.purchases.constant
  grant n hbase R hsheet hquote hNative hReadout P hpre hpost cap hcap hcap0 := by
    obtain ⟨H⟩ := E.grant n hbase R hsheet hquote hNative hReadout P hpre hpost
      cap hcap hcap0
    refine ⟨H.val.transported ?_⟩
    intro m
    change min (W.output.pair R.family (m - 1)) 1 =
      min (W.input.pair R.family (m - 1)) 1
    rw [hW]

def Specification.transported (S : Specification hG B J s q native) :
    Transported.Data hG B J s q native :=
  (S.chooseData (diagonalAllocation S.diagram)).transported
    (diagonalAllocation_output S.diagram)

omit [DecidableEq V] [Fintype V] in
/-- The stronger full hypothesis supplies the old interface by a proved allocation. -/
theorem ManuscriptApplication.transported (H : ManuscriptApplication G) :
    Transported.ManuscriptApplication G := by
  intro hG V instD instF B J s q native
  exact ⟨(chooseSpecification H hG B J s q native).transported⟩

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
  data r n : Data hG B (stage r n).request s q native
    (stage r n).selected.capacities (stage r n).selected.diagram (allocation r n)

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
  data r n := (specificationStage H hG B J s q native r n).selected.chooseData
    (stageAllocation H hG B J s q native r n)

/-- The exact physical-stage width equality used by the successor input. -/
theorem Chain.successor_width (S : Chain hG B J s q native) (r n : ℕ)
    (R : Run G) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family (S.allocation r (n + 1)).input)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (S.allocation r n).target R.family (m + 1) =
      (ActualRequestNumericSchedule.selected R hG hReadout
        (S.allocation r (n + 1)).input P (S.stage r (n + 1)).request
        cap hcap hcap0).inputWidth m :=
  Allocation.successor_width (S.allocation r n) (S.allocation r (n + 1)).input
    (S.adjacent r n) R hG hReadout P (S.stage r (n + 1)).request cap hcap hcap0 m

end YM.Integration.FullQLocal.PreRun.Profile
end
