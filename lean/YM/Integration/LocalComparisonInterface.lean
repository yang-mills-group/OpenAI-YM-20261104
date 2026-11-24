import YM.ComparisonDensity.Address.Metric
import YM.RG3.Script.Picnic.Taste
import YM.Bid.Fuels

/-!
Concrete representation vocabulary for the external local comparison lemma.

This file defines receipts, not a proof of local comparison. In particular,
`FullBudget` is a norm on a specified common representation. It does not take
an infimum over representations, and its witnesses precede the independent
test arguments. The field derivatives use factorial weights.
The actual transition below always uses the coupling of `C.path`, even when
a pre-reset carrier has a different displayed `Rep.beta`.

The independently prescribed formal step and its real rendering are bound in
the companion contract. No arbitrary physical density is declared to have a
small error merely because it has the same evaluated vacuum.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory
open RG3.Held RG3.Forms RG3.Script.Picnic
open Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X : Type*} {P : Rep G n} {o : V → Site n}

/-- The whole product of independently chosen unit tests. The orbit retains
the derivative order and polynomial position weight of each slot. -/
def IndependentTests (D : V → ComparisonDensity.Address.Orbit) :=
  ∀ v, {f : ComparisonDensity.Address.Pos → ℂ // (D v).Bill f 1}

/-- The ambient product test space used for multilinearity. -/
def TestSpace (D : V → ComparisonDensity.Address.Orbit) :=
  ∀ v, (D v).Mood

/-- Unit tests are evaluated in the same ambient space, without identifying
independent slots or replacing them by one common test. -/
def testInclusion (D : V → ComparisonDensity.Address.Orbit)
    (x : IndependentTests D) : TestSpace D :=
  fun v => ⟨(x v).val, ⟨1, (x v).property⟩⟩

/-- Passive pullback preserves the entire declared representation layout. -/
def pullback {Y : Type*} (f : Y → X) (T : Taste X o P R) : Taste Y o P R where
  menu :=
    { origins := T.menu.origins
      rays := T.menu.rays
      branch := T.menu.branch
      marks := T.menu.marks
      global := fun y => T.menu.global (f y)
      regular := fun y => T.menu.regular (f y)
      force := fun y => T.menu.force (f y) }
  root := T.root
  tag := T.tag
  site := T.site
  score := fun y => T.score (f y)

/-- Algebraic independent-slot dependence, including global mixed captions.
This is separate from norm bounds on the unit test product. -/
structure Multilinear (D : V → ComparisonDensity.Address.Orbit)
    (T : Taste (TestSpace D) o P R) : Prop where
  regular i U : Letter ℂ (fun v => (D v).Mood) (T.menu.rays i).val
    (fun x => T.menu.regular x i U)
  forced i j U : Letter ℂ (fun v => (D v).Mood) (T.menu.marks i j).val
    (fun x => T.menu.force x i j U)
  unit v : Letter ℂ (fun v => (D v).Mood) {v} (fun x => T.menu.global x v)
  captions i : Letter ℂ (fun v => (D v).Mood) (T.tag i).val
    (fun x => T.score x i)

/-- All declared test/stencil addresses are retained, including at zero test
values. Origins alone do not certify these larger supports. -/
structure Retains (T : Taste X o P R) (address : V → Support n) : Prop where
  origins v : o v ∈ address v
  regular i v : v ∈ (T.menu.rays i).val → address v ⊆ T.menu.branch i
  forced i j v : v ∈ (T.menu.marks i j).val →
    address v ⊆ (P.activities.forced i).support
  captions i v : v ∈ (T.tag i).val → address v ⊆ T.site i

/-- A common bound on each coefficient's factorial derivative norm.
The coefficient budget `b` is chosen before the independent test and root.
The derivative witnesses remain those of the native factorial norm; this
places no extra requirement on their simultaneous choice across tests. -/
structure RegularMajorant (p : BudgetPoint) (T : Taste X o P R)
    (i : ℕ) (b : ℝ) : Prop where
  controls (x : X) (v : V) (hv : v ∈ (T.menu.rays i).val) :
    Mix.grain p (T.menu.branch i) (T.menu.regular x i) (o v) b

/-- Complete regular/caption and divided marked-forced budget, on one fixed
layout. `p` may retain a prescribed support reserve above `P.p`.

The two separate totals match the regular and forced clauses of `qlocal`.
Every common coefficient majorant is chosen before `x : X`; no volume norm
equivalence or bound depending on the number of torus sites appears here.
-/
structure FullBudget (p : BudgetPoint) (T : Taste X o P R)
    (w : V → ℝ) (κ regularPrice forcedPrice : ℝ) where
  white : ℕ → ℝ
  black : ℕ × ℕ → ℝ
  gold : ℕ → ℝ
  unitBound : V → ℝ
  active (x : X) : (T.leaf x).Active
  radii v : 0 < w v
  divisor : 0 < κ
  white_nonnegative i : 0 ≤ white i
  regular i : RegularMajorant p T i (white i)
  regular_law (x : X) (i : ℕ) : p.Regular (T.menu.branch i) (T.menu.regular x i)
  black_nonnegative i : 0 ≤ black i
  forced (x : X) (i j : ℕ) (U : Config G n) :
    ‖T.menu.force x i j U‖ ≤ black (i, j)
  gold_nonnegative i : 0 ≤ gold i
  caption (x : X) (i : ℕ) : ‖T.score x i‖ ≤ gold i
  unit_nonnegative v : 0 ≤ unitBound v
  unit (x : X) (v : V) : ‖T.menu.global x v‖ ≤ unitBound v
  regularTotal (v : V) :
    ∃ B D : ℝ,
      SumBudget (fun i => if v ∈ (T.menu.rays i).val then
        Poly.toll w (T.menu.rays i) * p.mass (T.menu.branch i) (white i) else 0) B ∧
      SumBudget (fun i => if v ∈ (T.tag i).val then
        Poly.toll w (T.tag i) * p.mass (T.site i) (gold i) else 0) D ∧
      w v * unitBound v + B + D ≤ regularPrice
  forcedTotal (v : V) :
    SumBudget (fun i : ℕ × ℕ => if v ∈ (T.menu.marks i.1 i.2).val then
      Poly.toll w (T.menu.marks i.1 i.2) *
        p.mass (P.activities.forced i.1).support (black i) else 0)
      (κ * forcedPrice)

/-- A carrier on the given physical trajectory. The displayed coupling is
not silently identified with the physical coupling before reset. -/
structure Carrier (C : Family G) (N period level : ℕ) where
  rep : Rep G (C.side level period)
  path : rep.path = (C.path.rep N period level).path
  clip : rep.clip = (C.path.rep N period level).clip
  point : rep.p = C.path.levels.budget level
  vacuum : rep.eval = (C.path.rep N period level).eval

variable (C : Family G) (N period level : ℕ)

/-- The requested fixed derivative/distance orders and support reserve are
explicit. Threshold and block-cover geometry are those of the actual stage.
This is a binding of norm conventions, not a comparison estimate. -/
structure NormAt (p : BudgetPoint) (fieldOrder distanceOrder : ℕ)
    (supportExponent : ℝ) : Prop where
  threshold : p.threshold = (C.path.levels.budget level).threshold
  block : p.B = (C.path.levels.budget level).B
  order : p.order = fieldOrder
  distance : p.power = distanceOrder
  reserve : p.supportExponent = supportExponent

/-- The single marked-forced divisor of the actual output stage. -/
def forcedDivisor : ℝ :=
  Real.sqrt (C.path.levels.clock.forcedAllowance level)

/-- The literal full marked transition, before any quotient or logarithm.
Its beta is the actual trajectory beta and is independent of a carrier's
displayed kinetic coefficient. -/
def actualPush [Fintype V]
    (F : Config G (C.side (level + 1) period) → Poly R) :
    Config G (C.side level period) → Poly R :=
  (C.path.levels.clock.op level period).push
    (C.path.β N period (level + 1)) F

/-- Field-dependent normalization by the full actual coarse vacuum. -/
def normalized [Fintype V]
    (F : Config G (C.side level period) → Poly R)
    (U : Config G (C.side level period)) : Poly R :=
  ((C.path.rep N period level).eval U)⁻¹ • F U

variable {C N period level}

/-- Exact transition of an entire common representation. Both layouts and
their roots precede every independent test; no equality of label norms is
inferred from this full-density equation. -/
structure ExactStep [Fintype V]
    (Q : Carrier C N period (level + 1))
    (Q' : Carrier C N period level)
    (o : V → Site (C.side (level + 1) period))
    (o' : V → Site (C.side level period))
    (input : Taste X o Q.rep R) (output : Taste X o' Q'.rep R) : Prop where
  roots v : (C.path.levels.clock.op level period).ratio.parent (o v) = o' v
  density (x : X) : actualPush C N period level ((input.leaf x).density) =
    (output.leaf x).density

end YM.Integration.LocalComparison
