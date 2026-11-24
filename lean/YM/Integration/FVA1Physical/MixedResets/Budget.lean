import YM.Integration.FVA1Physical.MixedResets.LessonPaid
import YM.QuadraticLocal.Tariff.Facade
import YM.QuadraticLocal.Class.Feel
/-!
# Admission and sharpened costs at the original currencies, fixed on the declared interval
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
  (hi : m ≤ i) (below : i<b) (birth : b≤N) (L : Lesson (N:=N) R J D Q π Γ hi)
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
variable {Θ : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (w₀ : Θ → ℝ) (grades : Θ → ℕ) (school : School k) (e_E ηz : ℝ) (s sx : ℕ)
  (f : Pupil (Ψ (i+1)) R₀ (Affinity.Wallet allow)) 
local notation "p" => (school.order)
local notation "w" j:max => (Academy.wages R w₀ school.pieces j b)
local notation "φv" j:max => (σ).clock.hatBeta j
variable (ε η : ℝ) (hp : 0<ε) (hη : 4*ε ≤ η) (hh : ε ≤ 1/8)
  (hw : ∀ i, 0 < w₀ i)
  (t : Pupil (Ψ i) R₀ (Affinity.Wallet allow)) (F' : Tree.Forest (Route.step R i n).ratio)
local notation "here" => ( Stoop.radius w₀ (Sycamore.battery R school.pieces i b) )
local notation "level" j:max => Sycamore.life R j b school ε
local notation "q" => ((2:ℝ)^((p:ℝ)+1-4*ε) * (Route.coupling R N b n)^((p:ℝ)+1-η))
local notation "total" => ((φv b)^ε)
local notation "δ" => ((2*Route.coupling R N b n)^(2*sx))
local notation "B" => (Ψ i).p
local notation "B₀" => (Ψ (i+1)).p
local notation "fee" j:max => (min ((φv b)^ (-(sx:ℝ))*κ) (Real.sqrt (Time.quoteHard (σ) j (R.kit.book) (Ψ (i+1)).beta)))
local notation "X₁" => (σ).clock.forcedAllowance i
local notation "fPay" => (Real.sqrt (Time.quoteHard (σ) i (R.kit.book) (Ψ (i+1)).beta))
local notation "weightPay" => ((φv b)^ (-(sx:ℝ)))
local notation "alter" => ( Ψ b ).beta
set_option maxHeartbeats 840000
/-- The Mark local comparison budget in qelt currency on genuine `α` narration
and curvature powers, simultaneous with its local price. `fixed` @ true declared w.
'ε' pays for consumables AFTER original w budgets restored. `η≥4*ε`.
`wradius` pays both available gauges, stronger needed for divided K-off tests;
REAL forcedAllowance witness retained. `replenish_*` supplies before & after
in the currency used by the mathematical proof (strictly *temporary* rescaling
of the model and error budget, all at the actual w precision). `instructor` includes
the pre individual coefficient loss and when applicable the before-modelled
copy estimates on this reporter. `H` selects one core proof for every t etc.
The local `aid`/`billing` covers restoration EARLY or LATE separately; this course
does NOT feed that naive lift currency cost into the inductive sharp restored budget
(rebate can make naive much larger than g^(p+1-η) in that power!).
`fee1*fare` shown explicitly. `employ` below accompanies a `Session`, itself
with the `scoreS2`, `attendsS2` gates it uses; not a claim of pricing late bound only
from rough local price `Ω` without the finer proof. See the Shoot phase for local
post β-cost separately.
-/
structure Payment : Prop where
  instructor : ∃ e: Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ (w (i+1)) (Sycamore.life R (i+1) b school ε) f,
      InvoiceHistory R J D Q π Γ Ψ clock ahead hi (lt_of_lt_of_le below birth) L allow kills w₀ grades school (level (i+1)) ηz s f (Sycamore.battery R school.pieces (i+1) b) e F' t
  fixed : Full (Ψ i) w₀ κ t.packet 2 q δ
  fee1 : (Sycamore.battery R school.pieces (i+1) b)^school.pieces ≤ (φv b)^ ε
  fare : (Sycamore.battery R school.pieces i b)^(school.pieces) * (Sycamore.life R i b school ε) ≤ Sycamore.notice R b school (2*ε) ∧ Sycamore.notice R b school (2*ε) ≤ q
  wradius : t.packet.hard.Paid w₀ (B).B (B).supportExponent (fee i) ∧ fPay ≤ X₁
  salary : (Tint.Patrol.picture t.painter t.packet).E.Paid w₀ (B).B ((B).supportExponent+2) ((φv b)^ε) ∧ Earn.Scene.Armada t.painter w₀ grades (Poetry.Agenda.seed D φ (Burn.horizon k) I) (total) p school.pieces school.horizon
  replenish_now : Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ (w (i+1)) (Sycamore.life R (i+1) b school ε) f ∧ Sycamore.life R (i+1) b school ε ≤ 1
  replenish_after : Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ (w i) (Sycamore.life R i b school ε) t ∧ Sycamore.life R i b school ε ≤ 1

include conc hw hη hh
lemma Payment.accounted
    (z : Sycamore.Session (ε:=ε) R m b sx k school) (P₁ : Ribbon (φ:=φ) (i:=i+1) R D Ψ allow kills grades school Set.univ (w (i+1)) (Sycamore.life R (i+1) b school ε) f)
    (P'c : Ribbon (φ:=φ) (i:=i) R D Ψ allow kills grades school Set.univ (w i) (Sycamore.life R i b school ε) t)
    (P₀ : InvoiceHistory R J D Q π Γ Ψ clock ahead hi (lt_of_lt_of_le below birth) L allow kills w₀ grades school (level (i+1)) ηz s f (Sycamore.battery R school.pieces (i+1) b) P₁ F' t)
    (hr : Eraser.Registered R D Ψ (φ:=φ) (ε:=ε) (N:=N) (b:=b) allow kills grades school Set.univ f sx w₀ t) :
    Payment (i:=i) R J D Q π Γ Ψ clock ahead hi below birth L allow kills w₀ grades school ηz s sx f ε η t F' := by
  let x := later R π Γ Ψ conc ((Nat.le_succ_of_le hi).trans below) birth
  have init : alter ∈ RG.Shoot.band R.alloy.B.a b := x.beta.symm ▸ (R.T.sticks N n|>.prices _ (Nat.zero_le _) birth).2
  have hfee := (Graces.glyphBound (σ) i).1
  have hQ : (Ψ b).beta = (R.family.path.rep N n b).beta := x.beta
  have hg1 := Eon.lifeSpan R school sx ε η hη hh _ z.owns init; have hg2 := Eon.economies R school sx ε _ z.owns init
  have hv : Sycamore.notice R b school (2*ε) ≤ q := by unfold Route.coupling; rw [← hQ]; exact hg1
  have hδ : weightPay ≤ δ := by unfold Route.coupling; rw [← hQ]; exact hg2
  have hy : t.packet.hard.Paid w₀ (B).B (B).supportExponent ((φv b) ^ (-(sx:ℝ))*κ) := Hard.mono _ hr.safeguarded (min_le_left ..)
  have hh2 := P₀.certificate
  obtain ⟨J',h_,V',hP,P2,hV⟩ := hh2
  obtain ⟨pp,seed,k',h_,Mm,h₀,_hall,Hc,hs⟩ := P2.canon
  have Δ : (B).supportExponent+2=(B).supportExponent+1+1:= by ring
  refine ⟨⟨P₁,P₀⟩,⟨hfee,hw,?_, Hard.mono _ hy (mul_le_mul_of_nonneg_right hδ hfee.le)⟩,
    Sycamore.wax R school sx z (Nat.le_succ_of_le hi) below,
    ⟨Sycamore.attendsS2 R school sx z hi below.le,hv⟩,
    ⟨hr.safeguarded,Hc.strongest.2⟩, ⟨ ?_, hr.scale ⟩, ⟨P₁,z.owns.seat (i+1) (Nat.le_succ_of_le hi) below⟩, ⟨P'c,z.owns.seat i hi below.le⟩ ⟩
  · rw [Δ]; exact Lamps.loan_monotone _ (pay_all _ hr.score) hv
  rw [Δ]; exact hr.salary
end YM.Integration.FVA1Physical.MixedResets
