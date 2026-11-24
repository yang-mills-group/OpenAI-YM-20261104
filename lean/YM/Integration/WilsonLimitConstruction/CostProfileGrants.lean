import YM.Integration.FullQLocalCostProfileSpecification
import YM.Integration.WilsonLimitConstruction.WidthRescalingFloor
import YM.Integration.WilsonLimitConstruction.PrescribedGrantFloors

/-! Supply the external width rescaling of CostProfile.Data by finite native
pre-block requests while retaining the exact analytic grant and its raw rate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.CostProfileGrants

open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun FullQLocal.PreRun.Profile
open scoped Topology

variable {G : Gauge} {V : Type}
    {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}
    {D : Diagram s q native}

def strengthen (P : Purchases) (W : Allocation D) : Purchases :=
  { P with baseFloor := fun j => max (P.baseFloor j) (WidthRescalingFloor.floor W.input D.transport j) }

theorem floor_le (P : Purchases) (W : Allocation D) (J : Request V) :
    P.floor J s ≤ (strengthen P W).floor J s := by
  intro j
  exact max_le_max (le_max_left _ _) le_rfl

variable [DecidableEq V] [Fintype V] {B : Census V} {hG : G.Simple}
    {J : Request V} {caps : Handoff.OutputCapacities} {W : Allocation D}
    {e : CostProfile.Recipe}

/-- A stage already bought on the identity recipe yields its own original
profile data, preserving the exact purchase and physical grant. -/
def keepProfile (E : CostProfile.Data hG B J s q native caps D W e)
    (he : e = .keep) : Profile.Data hG B J s q native caps D W := by
  subst e
  exact E.forget

theorem keepProfile_purchases (E : CostProfile.Data hG B J s q native caps D W e)
    (he : e = .keep) : (keepProfile E he).purchases = E.purchases := by
  subst e
  rfl

/-- The analytic clause on the original floor. The width floor is computed
separately and its payment requires only the upper endpoint. -/
def Grants (P : Purchases) : Prop :=
  ∀ (n : ℕ → ℕ) (_ : s.floorL ≤ n) (R : Run G)
    (_ : R.metals.p = ThroughLaunch.raise s n)
    (_ : R.metals.K = ThroughLaunch.raging s q)
    (_ : NativeComponentRecipe.Realized s q native R.family.path.levels R.alloy.B.M)
    (readout : RG05Preconstruction.ReadoutPurchase R.b)
    (payment : WidthPayment R.family W.input)
    (_ : PaidProfile (P.pre J W) R.family.path.levels)
    (_ : PaidProfile (P.post (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0))
    (hsub : e.Subpower (ActualRequestNumericSchedule.selected
      R hG readout W.input payment J cap hcap hcap0)),
    Nonempty { H : Prescribed.Grant (Gamma := B) caps (RunFormalChain.fromRun R) J
      (e.schedule (ActualRequestNumericSchedule.selected R hG readout W.input payment J cap hcap hcap0) hsub)
      (P.floor J s) n P.constant (W.target R.family) //
      RawInherited.Receipt H.original.models.prices P.rawDegree P.rawCoefficient }

def of_grants (P : Purchases)
    (H : Grants (B := B) (hG := hG) (J := J) (caps := caps) (W := W) (e := e) P) :
    CostProfile.Data hG B J s q native caps D W e where
  purchases := strengthen P W
  rescaling n _ R hsheet _ m _ _ hhigh := by
    let j := R.family.path.levels.clock.J (m + 1)
    have hf : WidthRescalingFloor.floor W.input D.transport j ≤ n j :=
      (le_max_right (P.baseFloor j) _).trans
        ((RawInherited.floorRequest_preserves G J s.profile P.constant.value
          (strengthen P W).baseFloor j).trans hhigh)
    exact WidthRescalingFloor.on_run R s n hsheet W.input D.transport
      (fun i => (D.transport_pos i).le) m hf (W.target R.family m) (min_le_right _ _)
  grant n hb R hs hq hn hr wp hp hpost cap hc hc0 hsub := by
    obtain ⟨old⟩ := H n hb R hs hq hn hr wp hp hpost cap hc hc0 hsub
    exact ⟨⟨PrescribedGrantFloors.grant (floor_le P W J) old.val, old.property⟩⟩

/-- The output capacity/diagram choice may now be proved using only the grants
on each enlarged analytic domain and the raw rate on that grant's prices. -/
theorem specification (h :
    ∀ (W : Allocation D) (e : CostProfile.Recipe), ∃ P : Purchases,
      Grants (B := B) (hG := hG) (J := J) (caps := caps) (W := W) (e := e) P) :
    Nonempty (CostProfile.Specification hG B J s q native) := by
  refine ⟨⟨caps, D, ?_⟩⟩
  intro W e
  obtain ⟨P, hP⟩ := h W e
  exact ⟨of_grants P hP⟩

/-- Exact analytic content after removing the numerical width rescaling field.
Widths and the finite recipe are still selected before purchases. -/
def Application (G : Gauge) : Prop :=
  ∀ (hG : G.Simple) (V : Type) [DecidableEq V] [Fintype V]
    (B : Census V) (J : Request V) (s : Sheet G) (q : MapPrices)
    (native : NativeComponentRecipe.Choice s),
    ∃ (caps : Handoff.OutputCapacities) (D : Diagram s q native),
      ∀ (W : Allocation D) (e : CostProfile.Recipe), ∃ P : Purchases,
        Grants (B := B) (hG := hG) (J := J) (caps := caps) (W := W) (e := e) P

/-- The full preselection contract and the grant-only contract are equivalent.
The forward implication projects the chosen purchases. The reverse implication
strengthens their floors and reuses the prescribed model and its prices. -/
theorem application_iff (G : Gauge) : CostProfile.ManuscriptApplication G ↔ Application G := by
  constructor
  · intro H hG V instD instF B J s q native
    obtain ⟨S⟩ := H hG V B J s q native
    refine ⟨S.capacities, S.diagram, ?_⟩
    intro W e
    obtain ⟨E⟩ := S.realize W e
    exact ⟨E.purchases, E.grant⟩
  · intro H hG V instD instF B J s q native
    obtain ⟨caps, D, grants⟩ := H hG V B J s q native
    exact specification grants

end YM.Integration.WilsonLimitConstruction.CostProfileGrants
end
