import YM.Integration.FullQLocalPrescribedWidth
import YM.Integration.FullQLocalTransportedPreRun
import YM.Integration.FullQLocalRawInheritedRate

/-!
A two-stage specification of the assumed full manuscript qlocal clause.
Capacities and the finite strip/strict-edge diagram precede the width allocation.
The allocation precedes all floors, prices depending on block lengths, and the
single physical Run. Its output receipt belongs to the same canonical model as
its raw inherited-rate receipt.

This is a hypothesis interface. It does not prove qlocal, upgrade an old Data,
identify independently selected grants, or infer a packet receipt by reducing
its width. The external inherited-input width has a rescaling condition; the
finite internal diagram separately records strict same-mesh losses.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Profile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open LocalComparison
open scoped Topology BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

/-- Fixed finite component data, all selected before the width profiles.
The height certificate excludes strict same-mesh cycles. Both same-index and
one-stage lookahead edges are admitted by Allocation below. -/
structure Diagram (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) where
  count : ℕ
  output : Fin count
  height : Fin count → ℕ
  edge : Fin count → Fin count → Prop
  edge_height {a b} : edge a b → height a < height b
  loss : Fin count → Fin count → ℕ → ℝ
  loss_pos a b i : 0 < loss a b i
  grade : Fin count → ℕ
  strip : Fin count → ProfileWidths
  strip_native a i :
    (strip a).width i ≤ NativeComponentRecipe.width s q native (grade a) i
  inputStrip : ProfileWidths
  input_native i : inputStrip.width i ≤ (s.profile i).width
  transport : ℕ → ℝ
  transport_pos i : 0 < transport i

variable {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

/-- Actual profiles satisfying every preselected strip and strict same-mesh
margin. The external input-to-output rescaling inequality is purchased below
using the actual block length, rather than imposed as a same-mesh loss. -/
structure Allocation (D : Diagram s q native) where
  input : ProfileWidths
  component : Fin D.count → ProfileWidths
  input_strip i : input.width i ≤ D.inputStrip.width i
  component_strip a i : (component a).width i < (D.strip a).width i
  same_mesh a b (hab : D.edge a b) i j (hij : j = i ∨ j = i + 1) :
    D.loss a b i * (component b).width j < (component a).width i

variable {D : Diagram s q native}

/-- The designated output component retains its actual profile. -/
def Allocation.output (W : Allocation D) : ProfileWidths :=
  W.component D.output

/-- The old output at level m is the next input at level m-1.
The cap is exactly the cap used by the existing selected schedule. -/
def Allocation.target (W : Allocation D) (C : Family G) (m : ℕ) : ℝ :=
  min (W.output.pair C (m - 1)) 1

/-- Every finite internal reciprocal width is a pre-length numerical request.
The finite prefix retains the preceding and lookahead profile indices. -/
def Allocation.profileBill (W : Allocation D) (i : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (i + 2),
    ((W.input.width k)⁻¹ + ∑ a : Fin D.count, ((W.component a).width k)⁻¹)

/-- Only these finite purchases are chosen after an admissible allocation.
The post coefficient is a function of the eventual original block sequence. -/
structure Purchases where
  baseFloor : ℕ → ℕ
  basePre : ℕ → ℝ
  basePost : (ℕ → ℕ) → ℕ → ℝ
  constant : LocalComparison.Global.PreBlockConstant
  rawDegree : ℕ
  rawCoefficient : (ℕ → ℕ) → ℕ → ℝ

omit [DecidableEq V] [Fintype V] in
def Purchases.floor (P : Purchases) (J : Request V) (s : Sheet G) : ℕ → ℕ :=
  RawInherited.floorRequest G J s.profile P.constant.value P.baseFloor

omit [DecidableEq V] [Fintype V] in
def Purchases.pre (P : Purchases) (J : Request V) (W : Allocation D) (i : ℕ) : ℝ :=
  max |RawInherited.preRequest G J s.profile P.basePre i| (W.profileBill i)

def Purchases.post (P : Purchases) : (ℕ → ℕ) → ℕ → ℝ :=
  RawInherited.postRequest P.basePost P.rawCoefficient

/-- The exact two-stage continuation. Its scalar rescaling conclusion uses the
actual adjacent indices of the original Run. Its rich grant retains both the
prescribed output receipt and the raw rate on the identical selected K. -/
structure Data (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s)
    (caps : Handoff.OutputCapacities) (D : Diagram s q native) (W : Allocation D) where
  purchases : Purchases
  rescaling (n : ℕ → ℕ) (hbase : s.floorL ≤ n)
    (R : Run G) (hsheet : R.metals.p = ThroughLaunch.raise s n)
    (hquote : R.metals.K = ThroughLaunch.raging s q)
    (m : ℕ) (hm : 0 < m)
    (hlow : purchases.floor J s (R.family.path.levels.clock.J m) ≤
      n (R.family.path.levels.clock.J m))
    (hhigh : purchases.floor J s (R.family.path.levels.clock.J (m + 1)) ≤
      n (R.family.path.levels.clock.J (m + 1))) :
    2 * D.transport (R.family.path.levels.clock.J (m + 1)) *
        W.target R.family m ≤
      (R.family.path.levels.S.block m).val *
        min (W.input.pair R.family m) 1
  grant (n : ℕ → ℕ) (hbase : s.floorL ≤ n)
    (R : Run G)
    (hsheet : R.metals.p = ThroughLaunch.raise s n)
    (hquote : R.metals.K = ThroughLaunch.raging s q)
    (hNative : NativeComponentRecipe.Realized s q native
      R.family.path.levels R.alloy.B.M)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family W.input)
    (hpre : PaidProfile (purchases.pre J W) R.family.path.levels)
    (hpost : PaidProfile
      (purchases.post (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Nonempty { H : Numeric.Prescribed.Grant
      (Gamma := B) caps (RunFormalChain.fromRun R) J
      (ActualRequestNumericSchedule.selected R hG hReadout W.input P J cap hcap hcap0)
      (purchases.floor J s) n purchases.constant (W.target R.family) //
      RawInherited.Receipt H.original.models.prices
        purchases.rawDegree purchases.rawCoefficient }

/-- Fixed capacities and strip data precede every width allocation.
Only realize chooses width-dependent finite purchases. -/
structure Specification (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s) where
  capacities : Handoff.OutputCapacities
  diagram : Diagram s q native
  realize (W : Allocation diagram) :
    Nonempty (Data hG B J s q native capacities diagram W)

/-- Explicit full-q assumption retaining its two-stage width quantifiers.
All construction, calibration, and rough-input quantifiers remain inside Data. -/
def ManuscriptApplication (G : Gauge) : Prop :=
  ∀ (hG : G.Simple) (V : Type) [DecidableEq V] [Fintype V]
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s),
    Nonempty (Specification hG B J s q native)

/-- Select the finite specification, not a physical Run. -/
def chooseSpecification (h : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) : Specification hG B J s q native :=
  Classical.choice (h hG V B J s q native)

variable {hG : G.Simple} {B : Census V} {J : Request V}
    {caps : Handoff.OutputCapacities} {W : Allocation D}

/-- Select width-dependent data only after fixing its actual allocation. -/
def Specification.chooseData (S : Specification hG B J s q native)
    (W : Allocation S.diagram) : Data hG B J s q native S.capacities S.diagram W :=
  Classical.choice (S.realize W)

/-- The old canonical interface is a literal resource projection.
No old grant is chosen first and subsequently upgraded. -/
def Data.forget (E : Data hG B J s q native caps D W) :
    Complete.Data hG B J s q native where
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
    exact ⟨H.val.forget⟩

theorem Data.forget_widths (E : Data hG B J s q native caps D W) :
    E.forget.widths = W.input := rfl

theorem Data.forget_capacities (E : Data hG B J s q native caps D W) :
    E.forget.capacities = caps := rfl

omit [DecidableEq V] [Fintype V] in
/-- Equality of the two endpoint profiles gives equality of the actual
old output width and following selected input width, including their shift. -/
theorem Allocation.successor_width (W : Allocation D)
    (Wnext : ProfileWidths) (hnext : W.output = Wnext)
    (R : Run G) (hG : G.Simple) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family Wnext) (Jnext : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    W.target R.family (m + 1) =
      (ActualRequestNumericSchedule.selected R hG hReadout Wnext P Jnext
        cap hcap hcap0).inputWidth m := by
  change min (W.output.pair R.family (m + 1 - 1)) 1 =
    min (Wnext.pair R.family m) 1
  rw [Nat.add_sub_cancel, hnext]

end YM.Integration.FullQLocal.PreRun.Profile
end
