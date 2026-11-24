import YM.Integration.FVA1Physical.MixedResets.Graduation
import YM.Integration.FVA1Physical.MixedResets.Budget
/-!
# Connected budget and exact comparison through a chosen close itinerary

Core extension. `Payment` at every step of one chosen operator history. Sizes one
run of Mark Labels in the prescribed fixed load and powers. `Day` includes receipt
instructor, both before and calibrated reads (real `Ident`) at physical normalization,
unmarked gain `e`, all inherited marked discrepancies (for mixed use before physical
boosts). See Wallet frames & `Payment`. Restored reported size ≤
`2^(p+1-4*ε)*g_b^(p+1-η)` on actual and projected reading (latter when projected
through existing Tensor.Currency with its hypotheses). Force Price ≤ `(2*g_b)^(2*sx)`
in divided units and stronger table also. Both in original `w₀` of input EVEN IF path
purchased with temporarily smaller working currency. Reserve multiplier & eligibility
for reuse at next levels (`Session` buys in Teach). Actual fields, K and β unchanged.

`Learns` not charged vac.Step for A unaffected post-currency. Higher order internal
vac purchase applies on `Teach.Vac` below or `Concourse` & `Appearance`. In
addition, `R,G, R.alloy` from concrete supply, so `Consequence...` applies to it
if other reserve needed by consumers (not claimed HERE). We do not claim that if
starting with just model through precisely p (not extra internal vacuum supply) or
including `e^natural`, the same comparison will hold. All counts/orders/reps exact in types.
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

variable {G : Gauge} (R : Run G) {m n i k b N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (below : i<b) (birth : b ≤ N) (L : ∀ j, ∀ h:m ≤ j, j<b → Lesson (N:=N) R J D Q π Γ h)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "Uu" => (Ψ (i+1))
local notation "P'" => (Ψ i)
local notation "Gm" => (Coat.gStep ((Ψ i).beta))
local notation "Wc" => (Time.quoteHard (σ) i (R.kit.book) (Ψ (i+1)).beta)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep (Ψ (i+1)).beta
local notation "κ" => LocalComparison.forcedDivisor R.family i

open QuadraticLocal.Syl
open RG3 RG3.Annuncia
variable {Θ V : Type} [Fintype Θ] [DecidableEq Θ] [Fintype V] [DecidableEq V] {R₀ : Marker.Census V}
    (f₀ : Θ → V) {X : V → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    (atV : ∀ i, Set (X i)) (killV : ∀ i, Submodule ℝ (X i))
    (wV : V → ℝ) (hw : ∀ i, 0 < wV i) (η : V → ℕ) (school : School k)
    (uP : ∀ i:ℕ,i ≤ b → Earn.Passport (R.family.side i n) V) (ε ηz : ℝ) (s : ℕ)
    (H : ∀ i:ℕ, m ≤ i → i≤b→ Pupil (Ψ i) (Replica f₀ R₀) (Affinity.Wallet (fun i=>atV (f₀ i))))
local notation "allow" => (fun i => atV (f₀ i))
local notation "kills" => (fun i => killV (f₀ i))
local notation "grades" => (η ∘ f₀)
local notation "w₀" => (wV ∘ f₀)
local notation "Lh" => (L i hi below)
variable (sx : ℕ) (eta : ℝ)
  (Qp : Sycamore.Session (ε:=ε) R m b sx k school)
  (hps : 4*ε ≤ eta) (he : ε ≤ 1/8)
  (initial : Pupil (Ψ b) (Replica f₀ R₀) (Affinity.Wallet (fun i=>atV (f₀ i))))
  (Xb : Earn.Passport (R.family.side b n) V) (hXb : initial.address=Tariff.clone f₀ Xb)
  (hP : Academy.physicalCourse R Xb uP) (motive : m≤b)
  [Nonempty (Affinity.Wallet (fun i=> atV (f₀ i)))]
local notation "Tp" j:max => ( Pupil (Ψ j) (Replica f₀ R₀) (Affinity.Wallet allow) )
local notation "w" j:max => (Academy.wages R w₀ school.pieces j b)

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

abbrev Owns := Academy.Package R J D Q π Γ Ψ clock f₀ atV killV wV η school ahead sx ε Set.univ L initial birth H Xb hXb uP hP ηz s eta motive

structure Day : Prop where
  origin : ( H i hi below.le ).address=Tariff.clone f₀ (uP i below.le) ∧ ( H (i+1) (Nat.le_succ_of_le hi) below ).address=Tariff.clone f₀ (uP (i+1) below)
  witness (F₁ : Tree.Forest (Route.step R i n).ratio) : Payment (i:=i) R J D Q π Γ Ψ clock ahead hi below birth Lh allow kills w₀ grades school ηz s sx (H (i+1) (Nat.le_succ_of_le hi) below) ε eta ( H i hi below.le ) F₁

omit [Nonempty (Affinity.Wallet (fun i=> atV (f₀ i)))] in
def choice : Tree.Forest (Route.step R i n).ratio := Classical.choice (Tree.select _ ((Route.step R i n).patch.odd_side))
-- Need history also usable before choosing H. use Vertex.Game.Learners at any X. construction. No claims about all normalized permit stencils still without admissible representation.
local notation "dayTick" j:max h:max v:max => (Day R J D Q π Γ Ψ clock ahead (i:=j) h v birth L f₀ atV killV wV η school uP ε ηz s H sx eta)
-- include param's after selecting & stretching; retain loyalty, existence of such H
structure Graduate : Prop where
  prepared : Academy.Package R J D Q π Γ Ψ clock f₀ atV killV wV η school ahead sx ε Set.univ L initial birth H Xb hXb uP hP ηz s eta motive
  paid h₁ h₂ : H b h₁ h₂=initial
  punctual i' (h:m ≤ i') (v:i'≤b) : Ribbon (φ:=φ) (i:=i') R D Ψ allow kills grades school Set.univ (w i') (Sycamore.life R i' b school ε) (H i' h v)
  budgets i' (h:m ≤ i') (v:i'<b) : dayTick i' h v

include hw conc Qp hP hXb he hps

local notation "Diploma" => (Graduate R J D Q π Γ Ψ clock ahead birth L f₀ atV killV wV η school uP ε ηz s H sx eta initial Xb hXb hP motive)
local notation "Ξ" => Owns R J D Q π Γ Ψ clock ahead birth L f₀ atV killV wV η school uP ε ηz s H sx eta initial Xb hXb hP motive

lemma Graduate.adapt (hB : Ξ ) : Diploma := by
  obtain ⟨P,h⟩ := hB.stellar
  let h0 := P.educates
  refine ⟨hB,fun a c => h0.beginning,fun j hi hv => h0.teachers j hi hv,fun j hℓ ht => ?_⟩
  let Ψ' := h j hℓ ht
  refine ⟨⟨Ψ'.health, Ψ'.ancestor⟩,fun F' => ?_⟩
  obtain ⟨e,H'⟩ := matriculates R J D Q π Γ Ψ conc clock ahead hℓ ht birth L f₀ atV killV wV hw η school uP ε ηz s H F' (Ψ'.forever F')
  exact Payment.accounted R J D Q π Γ Ψ conc clock ahead hℓ ht birth (L j hℓ ht) allow kills w₀ grades school ηz s sx _ ε eta hps he (fun i=>hw (f₀ i)) _ F' Qp e (P.educates.teachers _ hℓ ht.le) H' (P.recording j hℓ ht).1

omit hw conc Qp hP hXb he hps
open Integration.LocalComparison
-- Induction through the actual steps. Makes chaining totally explicit without
-- asking for comparisons on unrelated replans. Budget caller can continue even
-- when b>cut? NO. Keep through all N. (future itinerary capture/OPE not asserted here).
-- Γ shift evaluated at actual prescribed coupling.
local notation "L₁" j:max h:max v:max=> ( L j h v )
local notation "portrait" v:max=> ( Tint.Patrol.picture (Pupil.painter v) ( Pupil.packet v ) )
local notation "Y1" j:max h:max v:max=> ( H j h v )

set_option maxHeartbeats 200000

inductive Trail : (j:ℕ) → (h:m ≤ j) → j ≤ b → Prop
  | start : H b motive le_rfl = initial → Trail b motive le_rfl
  | down {j : ℕ} (h : m ≤ j) (cut : j<b) (tm : Trail (j+1) (Nat.le_succ_of_le h) cut)
      (time : dayTick j h cut) : Trail j h cut.le

-- macro params Xb hXb or not? missing hP? use compiled check.
variable (track : Graduate R J D Q π Γ Ψ clock ahead birth L f₀ atV killV wV η school uP ε ηz s H sx eta initial Xb hXb hP motive)
include track hXb hP
local notation "wire" => (Trail R J D Q π Γ Ψ clock ahead birth L f₀ atV killV wV η school uP ε ηz s H sx eta initial motive)
-- Note `Wire` keeps H implicit positions.Finite; no claiming trail arbitrary chronology without membership Ψ+birth.
omit below in
lemma Graduate.whole (h:i≤b) : wire i hi h := by
  induction h using Nat.decreasingInduction with
  | self => exact Trail.start (track.paid _ _)
  | of_succ k h ih => exact Trail.down hi h (ih (Nat.le_succ_of_le hi)) (track.budgets k hi h)
end YM.Integration.FVA1Physical.MixedResets
