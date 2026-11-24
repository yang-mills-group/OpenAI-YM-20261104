import YM.Integration.FVA1Physical.MixedResets.LessonPaid
import YM.QuadraticLocal.Tariff.Learn
/-!
# No horizon assumptions on the repeat-step teacher

Take Lesson with **Replica** labels, so the estimate is still available even
where marker naming matters. Can take identity replication for the literal
finite Mark program. Importantly same Ψ on actual continuation; `.learn`
prepays both readings. (This is literal normalization on the Replica Census.
There are existing APIs for the moving V-valued readings of this, with
per-factor expenses for fixed loads, needed if requesting those in
addition/instead.)
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
local notation "cert" Y:max f:max => InvoiceHistory R J D Q π Γ Ψ clock ahead hi (lt_of_lt_of_le below birth)
    Lh allow kills w₀ grades school
    (Sycamore.life R (i+1) b school ε) ηz s (H (i+1) (Nat.le_succ_of_le hi) below)
    (Sycamore.battery R school.pieces (i+1) b) Y f (H i hi below.le)
variable (F' : Tree.Forest (Route.step R i n).ratio)
    [Nonempty (Affinity.Wallet (fun i=> atV (f₀ i)))]
local notation "f" => (H (i+1) (Nat.le_succ_of_le hi) below)
local notation "t" => (H i hi below.le)
local notation "g₁" => Coat.gStep (Ψ (i+1)).beta
local notation "w" => Academy.wages R w₀ school.pieces (i+1) b
local notation "e_E" => (Sycamore.life R (i+1) b school ε)
local notation "p" => (school.order)
local notation "cap" => (School.room school (PriceCompiler.step_paid R.alloy.B.a i) (J.trans (R.alloy.B.a.fits.mono hi)))
set_option maxHeartbeats 990000
include hw conc F' birth hi below

lemma matriculates (learn : Academy.Learn R J D Q π Γ Ψ clock hi f₀ atV killV wV η school ahead ε Set.univ L birth H below uP ηz s F') :
    ∃ e : Ribbon (φ:=φ) (i:=i+1) R D Ψ allow kills grades school Set.univ w e_E f, cert e F' := by
  obtain ⟨e,J',hv,Vnew,pe,hE,hf,hp⟩ := learn.projection
  letI := hv
  let earned := e.seed.total
  let a := ( voters R J D Ψ (φ:=φ) hi allow kills w grades school 1 1 f e.seed )
  let o := (f).address
  let cut := lt_of_lt_of_le below birth
  -- preserve M/Fv threshold in this replica specialization
  obtain ⟨pre,se,hCand,K',hb,Mm,Ht,-,-⟩ := pe.witnesses.pre
  let c := pe.witnesses
  letI := hb
  have her := pay_all _ e.clean
  have cal := post_price R J D Q π Γ Ψ conc clock ahead hi cut Lh cap o allow kills (f).painter (f).packet w grades p school.horizon e_E 1 ηz s a Vnew
    c.actual c.localCost earned her e.seed.policy
  have bill := joined R J D Q π Γ Ψ conc clock ahead hi cut Lh cap o allow kills (f).painter (f).packet w grades p school.horizon e_E 1 ηz s F' a Vnew
    cal pre se K' Mm hCand Ht.first earned her e.seed.policy
  refine ⟨e,?_⟩
  exact MixedResets.accounting R J D Q π Γ Ψ clock ahead hi cut Lh allow kills w₀ grades school e_E ηz s f (battery R school.pieces (i+1) b) e (fun i => hw (f₀ i)) (charged R) F' t Vnew hE bill
end YM.Integration.FVA1Physical.MixedResets
