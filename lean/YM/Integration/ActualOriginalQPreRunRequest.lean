import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.ActualRequestNumericSchedule

/-!
The original full-Q request is available before the native Run is chosen.
Every Run uses the same foundational frames and local sections. The finite
curvature presentation differs only in proof arguments, so its complete
monomial row alphabet and exact maximum rank are unchanged. No upper-degree
estimate, row deletion, or replacement observable is used here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOriginalQPreRunRequest
open Filter Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders
open scoped Classical Topology

variable {G : Gauge}

/-- The foundational section and its valuation precede every clock. -/
def presentation (G : Gauge) (d : ℕ) :
    ActualRunCurvaturePackets.Presentation (Next.Foundations.localSection G d) :=
  ActualRunCurvaturePackets.ofSection (Next.Foundations.localSection G d)
    (Next.Foundations.sound G d) (Next.Foundations.valuation G d)

theorem presentation_eq (R : Run G) (d : ℕ) :
    ActualRunCurvaturePackets.ofRun R d = presentation G d := rfl

variable {B : MS.Local.Physical.Deck G} {V : Type}
  [DecidableEq V] [Fintype V] (u : V → MS.Rake.Label B)

/-- All original slots, coordinates and supported monomials are retained. -/
abbrev Row :=
  (s : Slot u) × (j : ((Labels.frames G).level s.2.size).Index) ×
    ↥(((presentation G s.2.size).data.shape j).support)

omit [DecidableEq V] [Fintype V] in
theorem row_eq (R : Run G) :
    ActualOriginalQPackets.Row (R := R) u = Row u := rfl

def rankCap : ℕ :=
  let e := (Fintype.equivFin (Row u)).symm
  Finset.univ.sup (fun k => (e k).2.2.val.sum fun _ n => n)

omit [DecidableEq V] in
theorem rankCap_eq (R : Run G) :
    ActualOriginalQLayout.rankCap R u = rankCap u := rfl

/-- The exact finite Request used by the initial Q application, before Run. -/
def request (J : Request V) : Request V :=
  { J with
    vacuumRankCap := max J.vacuumRankCap (J.order + 2)
    inputPacketRankCap := max J.inputPacketRankCap (rankCap u)
    inheritedConstant := max J.inheritedConstant
      ((2 : ℝ) ^ ((J.order : ℝ) + 1 - J.eta))
    inherited_constant_nonnegative :=
      J.inherited_constant_nonnegative.trans (le_max_left _ _)
    tests := fun i => QlocalNativeTests.orbit (J.tests i).D 0
    test_order := J.test_order }

omit [DecidableEq V] in
theorem request_eq (R : Run G) (J : Request V) :
    ActualOriginalQPointSetup.request R u J = request u J := rfl

omit [DecidableEq V] in
/-- The bounded schedule is literally the one consumed by InitialSelection. -/
theorem schedule_eq (R : Run G) (hG : G.Simple) (J : Request V)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    ActualOriginalQInitialInput.schedule R hG u J
      (ActualRequestNumericSchedule.atRun R hG hReadout W P J cap hcap hcap0) =
    ActualRequestNumericSchedule.selected R hG hReadout W P (request u J)
      cap hcap hcap0 := rfl

end YM.Integration.ActualOriginalQPreRunRequest
end
