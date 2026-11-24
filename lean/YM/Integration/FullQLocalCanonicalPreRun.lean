import YM.Integration.FullQLocalPreRunApplication
import YM.Integration.FullQLocalCanonicalForcedOutput

/-!
The full manuscript application hypothesis with the final canonical forced
reserve retained. All finite choices still precede the original Run. The
existing resource construction may use Data.forget, while the application
keeps the complete Data and invokes its own grant on that identical Run.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Complete
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric.Retained
open LocalComparison
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

/-- The same finite choices, with the complete final-output continuation. -/
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
    Nonempty (FullQLocal.RenderedStep.Numeric.Canonical.CompleteGrant
      (Gamma := B) capacities (RunFormalChain.fromRun R) J
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


/-- Preserve every finite pre-Run choice for the existing resource
construction. The complete data itself is retained for its later grant. -/
def Data.forget {hG : G.Simple} {B : Census V} {J : Request V}
    {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}
    (D : Data hG B J s q native) : PreRun.Data hG B J s q native where
  widths := D.widths
  widths_le := D.widths_le
  floor := D.floor
  preRequest := D.preRequest
  postRequest := D.postRequest
  capacities := D.capacities
  constant := D.constant
  grant n hbase R hsheet hquote hNative hReadout P hpre hpost cap hcap hcap0 := by
    obtain ⟨H⟩ := D.grant n hbase R hsheet hquote hNative hReadout P hpre hpost
      cap hcap hcap0
    exact ⟨H.forget⟩

omit [DecidableEq V] [Fintype V] in
/-- The complete assumption implies the old application hypothesis.
Rechoosing old data from this implication does not retain its complete lift. -/
theorem ManuscriptApplication.forget
    (h : ManuscriptApplication G) : PreRun.ManuscriptApplication G := by
  intro hG V instD instF B J s q native
  obtain ⟨D⟩ := h hG V B J s q native
  exact ⟨D.forget⟩

/-- Choose the complete pre-Run data once, before constructing the Run. -/
def chooseData (h : ManuscriptApplication G) (hG : G.Simple)
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s) : Data hG B J s q native :=
  Classical.choice (h hG V B J s q native)

end YM.Integration.FullQLocal.PreRun.Complete
end
