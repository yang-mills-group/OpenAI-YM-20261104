import YM.Integration.ActualRequestNumericSchedule
import YM.Integration.FullQLocalRetainedGrant
import YM.Integration.ActualRunNativeComponentRecipe

/-!
This module applies the full quasi-local estimate as an explicit hypothesis.

The finite request, original Sheet, quote and native component choice precede
the selected widths, block floors, finite pre/post-length costs and output
constants. Only then is a matching original Run admitted. The exported Grant
uses the literal requested-norm schedule built from those selected widths;
there is no quantification over arbitrary NumericSchedule values.

The finite internal component graph and its two neighboring-index uses are
covered by the selected floors and cost requests. The complete Grant retains the actual short-hull and local-floor domain,
full mixed analytic input, complete output/remainder, and all later loss and
forced-order requests. The applied native intake is a restriction of the
supplied full lemma; it does not replace or assert a new weak-input theorem.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric.Retained
open LocalComparison
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

/-- One fixed profile request, paid before every later cutoff and period. -/
def PaidProfile (f : ℕ → ℝ) (A : Levels G) : Prop :=
  ∃ first : ℕ, ∀ m, first ≤ m → ∀ i, i ≤ A.clock.J (m + 1) →
    |f i| ≤ 1 + Real.log (Real.log (A.clock.hatBeta m))

/-- The finite analytic choices are data before the block lengths or clock.
The continuation is precisely the application projection assumed from the
full manuscript lemma, at the selected and numerically constructed schedule. -/
structure Data (hG : G.Simple) (B : Census V) (J : Request V)
    (s : Sheet G) (q : MapPrices) (native : NativeComponentRecipe.Choice s) where
  widths : ProfileWidths
  widths_le i : widths.width i ≤ (s.profile i).width
  floor : ℕ → ℕ
  preRequest : ℕ → ℝ
  postRequest : (ℕ → ℕ) → ℕ → ℝ
  capacities : Handoff.OutputCapacities
  constant : LocalComparison.Global.PreBlockConstant
  grant (n : ℕ → ℕ) (hbase : s.floorL ≤ n)
    (R : Run G)
    (hsheet : R.metals.p = ThroughLaunch.raise s n)
    (hquote : R.metals.K = ThroughLaunch.raging s q)
    (hNative : NativeComponentRecipe.Realized s q native
      R.family.path.levels R.alloy.B.M)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family widths)
    (hpre : PaidProfile preRequest R.family.path.levels)
    (hpost : PaidProfile
      (postRequest (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Nonempty (Grant (R := B) capacities (RunFormalChain.fromRun R) J
      (ActualRequestNumericSchedule.selected R hG hReadout widths P J cap hcap hcap0)
      floor n constant)

/-- The full-q application hypothesis.
All finite data precede the sole native construction. No assertion about an
arbitrary pre-existing Run or an arbitrary numerical schedule is made. -/
def ManuscriptApplication (G : Gauge) : Prop :=
  ∀ (hG : G.Simple) (V : Type) [DecidableEq V] [Fintype V]
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s),
    Nonempty (Data hG B J s q native)

end YM.Integration.FullQLocal.PreRun
end
