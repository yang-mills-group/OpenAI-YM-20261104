import YM.Integration.FVA1Physical.MixedResets.Receipt
import YM.QuadraticLocal.Relative.Newhall

/-!
# Unmarked discrepancy on the Calendar witness

This witness is a true full-field re-expression of the pushed polynomial;
not necessarily calibrated to the continuing trajectory. Useful e.g. BEFORE extracting
any kinetic/coupling value and doing that reset. Works with arbitrary incoming U in the
full native certified form (higher internal orders supplied).

Carry costs and **where they appear** the analytic extra packets of the vacuum. Predicted
answers are on a `paneling` P', use old U's beta-dependent push (NOT any oracle/prediction
instead as measure parameter). Use Vacancy below for the readiness and cost at output. No claim
here for further extraction of `U` that is not on the actual running path, or for validity of input
just given in density-equality form (hypothesis on the split of the model and residual
in native stencil grammar). All currents numerical costs are on geometry `BudgetPoint`
of the actual trajectory. K kept entire incl expansive multiplicity. No reuse of the
panel discrepancy's estimate on the calibrated presentation of the *same* answer without
a separate proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
  (U : RG.Rep G (R.family.side (i+1) n))
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "JJ" => R.alloy.B.a.clock.J
local notation "Y" => JJ (i+1)
local notation "I" => JJ i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "Φ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "C" => R.alloy.B.a.budget i
local notation "s" => R.metals.p.profile I
local notation "Gv" => R.kit.v Y I
local notation "cLink" => R.family.side i n
attribute [local irreducible] Till.Tilt.sundry
local notation "M₀" j:max W:max Qp:max => WheelP.M0 k 0 W (π j) Qp
variable (hp : RG.Shoot.Lives (WheelP.neutral R.alloy).bake N (i+1) n U)
  (hband : U.beta ∈ RG.Shoot.band R.alloy.B.a (i+1)) (e : ℝ)
  (mySeed : Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) U.beta))
  (hE : Burn.Candor (R.alloy.B.a.budget (i+1)) U.activities (Set.range mySeed.model) (Burn.silver (R.alloy.B.a.clock.hatBeta (i+1))) e)
  (F₁ : Tree.Forest (Route.step R i n).ratio) (V : Locator.Calendar R J D Q π Γ hi L (U:=U) e F₁) (p : ℕ)

local notation "ℓ" => R.rolls.L Y
local notation "v" => (WheelP.coefficientLoss s Gv ℓ (Φ))
local notation "d₀" => ( WheelP.finalPrice s k ℓ Gv e (Φ) )
local notation "C'" => (Locator.paneling R J D Q π Γ hi L V.listing V.source U.beta V.scalar)
local notation "W₁" => ( Time.forecastK (σ) i (R.kit.scout) U.beta )
local notation "W₂" => ( Time.quoteHard (σ) i (R.kit.book) U.beta )
local notation "Logs" => (C').activities
local notation "g" => Coat.gStep U.beta
local notation "Cal" => Route.calibrator R D Q J π Γ hi L

/-- Budget on the `day` part = residual IN THE ANSWER. Model part `pivot`.
Values specified before applying the regular masks. Do not neglect the forced
history partners of the new analytic representation. K costs on same presentation.

Exponent convention `Local.cheap` = `Quotes.early` (supportExponent +3 on anchored norm),
stronger than the `Local.unweighted` bound. Access explicitly on the `day` stencil
here (and see also `Dusk.lineage`). -/
structure Vacancy : Prop where
  actual : ( C' ).eval=(Route.step R i n).push U.beta U.eval
  working : U.p=(Fμ) ∧ (C').p=(C) ∧ U.clip=Route.clip R N (i+1) n ∧ U.path=Route.action R N (i+1) n ∧
    (C').clip=Route.clip R N i n ∧ (C').path=Route.action R N i n
  reset : Wheel.now (Γ i) (Burn.horizon k+2) U.beta = (C').beta ∧ (C').beta= U.beta * (Cal).tariff (Burn.horizon k+2) (Coat.gStep U.beta)
  former y : (Logs).reg (Burn.pivot (R.family.side i n) y) = Burn.spine C y ∧
    (Logs).E (Burn.pivot (R.family.side i n) y) = (M₀ i (C) ((C').beta)) cLink y
  extra : Nonempty (Burn.Seed (C') (M₀ i (C) ((C').beta)))
  layout : Locator.Impress R (k:=k) (i:=i+1) π U U.beta ∧ Locator.Impress R (k:=k) (i:=i) π (C') (C').beta
  rooted j : (Logs).reg (Rosary.Guard.Dusk.day (R.family.side i n) j) = V.listing.reg j ∧
    (Logs).E (Rosary.Guard.Dusk.day (R.family.side i n) j) = V.source.logRead j
  allocated : Collection.Local V.listing C V.source d₀ W₁
  strong : (Logs).KBound C W₂ ∧ (Logs).ForcedFamily C
  gain : d₀ ≤ (2*g)^(p+1) + v*e
  gate : v ≤ Time.credit G (s)/8 ∧ Time.credit G (s)/8 ≤ (1:ℝ)/512

include F₁ cut V hp conc
set_option maxHeartbeats 640000
lemma derive_vacancy
    (h : Locator.Continuum R J D Q π Γ Ψ hi L (U:=U) (n:=n) e mySeed F₁ V p) : Vacancy R J D Q π Γ hi L U e F₁ V p := by
  let Qp := C'; let t := h.mark
  have hb := Locator.Calendar.coupled R J D Q π Γ hi L e hp F₁ V
  let pz := h.pace
  let a := avatar R π Γ Ψ conc hi cut.le
  let b := avatar R π Γ Ψ conc (Nat.le_succ_of_le hi) cut
  have tx : Time.credit G (s) ≤ 1/64 := by simpa only [one_div] using (Time.authorized G (s)).1
  refine ⟨ hb.1, ⟨ hp.point,rfl,h.cloth.2.2.trans b.clip,h.cloth.1.trans b.path,h.pole.2.2.trans a.clip,h.pole.1.trans a.path⟩,
    ⟨pz.1.trans pz.2.1.symm,pz.2.1.trans pz.2.2⟩,?_,?_,h.nowPose,?_,t.herr,?_, h.budget.1, ⟨h.budget.2,by linarith only [tx]⟩ ⟩
  · intro y
    rw [h.pace.2.1]
    have hy := t.former y
    rw [h.listing.2] at hy ⊢
    exact hy
  · rw [h.pace.2.1]
    have hy := t.mirrors; rw [h.listing.2] at hy ⊢; exact hy
  · intro j
    have hy := t.rooted j; rw [h.listing.2] at hy; exact hy
  have hh := t.ethnic
  have hy := t.quote
  rw [h.listing.2] at hy hh
  exact ⟨hy,hh⟩
end YM.Integration.FVA1Physical.MixedResets
