import YM.Integration.FullQLocalProfileSpecification
import YM.Integration.FullQLocalCostProfileNumerics

/-!
Finite polynomial admitted-envelope recipes in the assumed full qlocal clause.
The recipe follows the actual width allocation and precedes the purchases and
the sole physical Run. It is not an arbitrary numerical schedule.

Only admittedCost changes. The actual subpower certificate remains a numerical
inlet; no estimate or compatibility with an already chosen old Grant is inferred.
The keep recipe projects literally to the preserved profile specification.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Profile
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}

variable [DecidableEq V] [Fintype V]
    {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

/-- Widths and a finite admitted-envelope recipe precede the original
purchases. The resulting Grant and raw-rate receipt share one model family. -/
structure Data (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s)
    (caps : Handoff.OutputCapacities) (D : Diagram s q native)
    (W : Allocation D) (e : Recipe) where
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
      (R.family.path.levels.S.block m).val * min (W.input.pair R.family m) 1
  grant (n : ℕ → ℕ) (hbase : s.floorL ≤ n)
    (R : Run G) (hsheet : R.metals.p = ThroughLaunch.raise s n)
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
    (hcap0 : Tendsto cap atTop (𝓝 0))
    (hsub : e.Subpower
      (ActualRequestNumericSchedule.selected R hG hReadout W.input P J cap hcap hcap0)) :
    Nonempty { H : Prescribed.Grant
      (Gamma := B) caps (RunFormalChain.fromRun R) J
      (e.schedule
        (ActualRequestNumericSchedule.selected R hG hReadout W.input P J cap hcap hcap0)
        hsub)
      (purchases.floor J s) n purchases.constant (W.target R.family) //
      RawInherited.Receipt H.original.models.prices
        purchases.rawDegree purchases.rawCoefficient }

/-- The finite polynomial recipe is fixed after widths and before every
purchase, output price, and physical Run. -/
structure Specification (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s) where
  capacities : Handoff.OutputCapacities
  diagram : Diagram s q native
  realize (W : Allocation diagram) (e : Recipe) :
    Nonempty (Data hG B J s q native capacities diagram W e)

/-- Explicit finite-envelope version of the assumed full manuscript clause.
The hypothesis is not derived from a previously chosen weaker specification. -/
def ManuscriptApplication (G : Gauge) : Prop :=
  ∀ (hG : G.Simple) (V : Type) [DecidableEq V] [Fintype V]
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s),
    Nonempty (Specification hG B J s q native)

def chooseSpecification (h : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) : Specification hG B J s q native :=
  Classical.choice (h hG V B J s q native)

variable {hG : G.Simple} {B : Census V}
    {caps : Handoff.OutputCapacities} {D : Diagram s q native}
    {W : Allocation D}

def Specification.chooseData (S : Specification hG B J s q native)
    (W : Allocation S.diagram) (e : Recipe) :
    Data hG B J s q native S.capacities S.diagram W e :=
  Classical.choice (S.realize W e)

/-- The identity recipe retains exactly the old schedule and purchases. -/
def Data.forget (E : Data hG B J s q native caps D W .keep) :
    Profile.Data hG B J s q native caps D W where
  purchases := E.purchases
  rescaling := E.rescaling
  grant n hbase R hsheet hquote hNative hReadout P hpre hpost cap hcap hcap0 :=
    E.grant n hbase R hsheet hquote hNative hReadout P hpre hpost cap hcap hcap0
      (Recipe.keep_subpower _)

def Specification.forget (S : Specification hG B J s q native) :
    Profile.Specification hG B J s q native where
  capacities := S.capacities
  diagram := S.diagram
  realize W := ⟨(S.chooseData W .keep).forget⟩

theorem Specification.forget_data (S : Specification hG B J s q native) :
    S.forget.capacities = S.capacities ∧ S.forget.diagram = S.diagram :=
  ⟨rfl, rfl⟩

end YM.Integration.FullQLocal.PreRun.CostProfile
end
