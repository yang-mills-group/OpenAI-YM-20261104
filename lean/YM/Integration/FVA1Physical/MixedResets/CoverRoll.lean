import YM.Integration.FVA1Physical.MixedResets.MarkedFK
import YM.QuadraticLocal.Poetry.Fish
import YM.QuadraticLocal.Echo.Sara

/-!
# Exact matching of a whole invoice of invariant roll kernels to the cover Wilson prescription

Separate pins, through the entire finite mark order. Allows any field and all periods
with Ad; retains the kernel even at arbitrary positions/separation/winding on the real torus.
Set up earlier than the physical estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Filter Function Finset Lattice RG Wilson Marker Precision Tree Input
open Push Uniform Next.SectorChange
open Comparison.RG02
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Sunrise
open scoped Classical Topology BigOperators
open AllOrder.Floe.Step.PlanV Pressure Gauge
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero

variable {G : Gauge} {assets : Metals G} {D : Rolls assets.p}
  {cal : Roots (G := G) assets.p.profile assets.K assets.p.kernel} {x y k : ℕ} {hx : 4 ≤ x}

set_option quotPrecheck false
local notation "P" => Mural.sheet assets.p D hx
local notation "K" => assets.p.kernel
local notation "O" => assets.O
local notation "C" => (assets.p.profile x).clip
local notation "T" => AllOrder.Floe.Step.tape (k+2)

variable {V : Type} [Fintype V] [DecidableEq V] {ι : Type} [Nonempty ι]
  {income : Income D cal x y hx k} {budget : V → Loan} {front : V}
  {card : ι → Card D cal x y hx k}
  {atom : ι → ∀ i : V, Atom G (budget i).r} {off : ι → V → Site (D.L x)}
  {ℓ p r : ℕ} {publication : ℕ → ι → Ink.Field (Coarse G ⊕ V)}
  {rolls : ℕ → ι → Poetry.Roll G V}

variable (printed : Income.Rendered D cal x y hx income budget univ front card atom off p ℓ publication rolls)

local notation "𝒫" i:max => (card i).self.north
local notation "𝒜" i:max => (card i).extra
local notation "a" => Poetry.Agenda.waist cal k x
local notation "C₀" i:max => card i
local notation "F" i:max => connectedBill K O (𝒫 i) C (𝒜 i) T budget (atom i) P (off i) p r
local notation "W" => Aviary.window P K C O (fun i:ι=> (card i).self.north) (fun i:ι=> (card i).self.paid)
    income.frame (fun i:ι=> (card i).self.upCost) assets.oga (fun i=> income.tools (card i))
    (fun i=> income.efficient (card i)) (Card.extra ∘ card) T budget atom off (univ:Finset V)

include printed

private theorem identifies_dock (i : ι) (order : r ≤ p) (n : Side) (hn : Ad G P K n) :
    (F i) n = (↑) ∘ (W r i n) := by
  have hc := kernel_exists income (card i) hn
  rw [connectedBill, dif_pos hc]
  funext z
  let zz := desks (Coarse G) V n z
  have one := (Aviary.publication P K C O (fun i:ι=> (card i).self.north)
    (fun i:ι=> (card i).self.paid) income.frame (fun i:ι=> (card i).self.upCost) assets.oga
    (fun i=> income.tools (card i)) (fun i=> income.efficient (card i)) (Card.extra ∘ card)
    T (fun i=> audited D cal x y hx (card i)) (fun i=> (card i).self.paid) budget atom off univ
    ⟨front, mem_univ _⟩ printed.reads printed.shells (Poetry.Agenda.belt_p cal k x) order i n
    (label (dock P K n)) hc.some zz.2 hn).1 p order zz.1
  exact one.trans (congr_arg (Complex.ofReal ∘ (W r i n)) (pair_mingle z))

/-- Exact *finite* interpretation of the approximand in `Painted.earned` on an arbitrary
admitted `S`, in particular in actual geometry rather than the dock. The cover construction
uses the very same finite Fk prescription: no dependence on the auxiliary regulator choices. -/
theorem connectedFK_eq_bill (i : ι) {n f : Side} {S : StepData n f}
    (hP : S.patch = Mural.sheet assets.p D hx) (hK : S.kernel = assets.p.kernel)
    (hm : Larger (G:=G) S) (g : Bulk.Kernel S C (𝒫 i) O)
    (Y : Forest S.ratio) (t : S.Choices) (z : rule (Coarse G ⊕ V) n)
    (invariant : ∀ v : V, (atom i v).Invariant) (order : r ≤ p) :
    connectedFK O (𝒫 i) C (𝒜 i) T p r g Y t budget (atom i) (QuadraticLocal.Echo.Sara.seat P S hP (off i)) z
      = (F i) n z := by
  rw [identifies_dock printed _ order n (Wheel.Ride.scope_complete S hP hK hm)]
  let B : BudgetPoint := ⟨2,6,1,1,1,le_rfl,le_rfl,by norm_num,by decide,by norm_num,le_rfl⟩
  let zz := desks (Coarse G) V n z
  have fv := QuadraticLocal.Echo.Sara.voucher P K O (fun i:ι=> (card i).self.north)
    (fun i:ι=> (card i).self.paid) income.frame (fun i:ι=> (card i).self.upCost) assets.oga
    (fun i=> income.tools (card i)) (fun i=> income.efficient (card i)) (Card.extra ∘ card) T
    (fun i=> audited D cal x y hx (card i)) (fun i=> (card i).self.paid) budget atom off
    ⟨front, mem_univ _⟩ printed.reads printed.shells i zz.1 zz.2 B order
    (Poetry.Agenda.belt_p cal k x) invariant
    S hP hK _ _ _ _ _ _ hm rfl rfl rfl rfl rfl rfl g Y t
  exact fv.trans (congr_arg (Complex.ofReal ∘ (W r i n)) (pair_mingle z))

/-- Every pinned Laurent bill equals precisely the normalized limit of the Fk
connected bill. We use the entire mixed mask. -/
theorem exact_heat (i : ι) {n : Side} (z : rule (Coarse G ⊕ V) n) (order : r ≤ p) :
    ((publication r i).table n z : ℂ) = onCover (F i) z ∧
    ∀ (S : ℕ → Side) (tiles : ℕ → ℕ) (w : ∀ i, Macrame.Window n (S i) (tiles i)),
      (∀ i, 0 < tiles i) → Tendsto (fun i => (S i).val) atTop atTop →
      Tendsto (fun j => tileAt (F i) (w j) z) atTop (𝓝 ((publication r i).table n z : ℂ)) := by
  obtain ⟨μ, _, cost⟩ := printed.reads.toMarquis.pay r order
  obtain ⟨f, hf, residual⟩ := printed.reads.earned r order
  have hA : Often (Ad G P K) := dock_larger P K (assets.p.has P)
  have cmp : Ink.Money.Pert (Ad G P K) (W r i) (publication r i) (Poetry.Agenda.poll cal k x) (μ i)
      (f i) (Aviary.plusK budget univ r + 2) := ⟨cost i, residual i⟩
  have pulse := Ink.Echo.scaleLean hf.grade i
  exact ⟨published_eq_cover cmp pulse printed.reads.pos hA (identifies_dock printed i order) z,
    fun _ _ w pos h => cover_tendsto w h pos cmp pulse printed.reads.pos hA (identifies_dock printed i order) z⟩

theorem exact_roll (i : ι) {n : Side} (field : rule (Coarse G) n) (pins : rule V n)
    (hn : Ad G P K n) (order : r ≤ p) :
    (Aviary.production (fun j => rolls j i) p r n field pins : ℂ) =
      coverImpulse K O (𝒫 i) C (𝒜 i) T budget (atom i) («P»:=P) (off i) p r pins field := by
  have kd := (kernel_exists income (card i) hn).some
  have eqn := (Aviary.publication P K C O (fun i:ι=> (card i).self.north)
      (fun i:ι=> (card i).self.paid) income.frame (fun i:ι=> (card i).self.upCost) assets.oga
      (fun i=> income.tools (card i)) (fun i=> income.efficient (card i)) (Card.extra ∘ card) T
      (fun i=> audited D cal x y hx (card i)) (fun i=> (card i).self.paid) budget atom off univ
      ⟨front, mem_univ _⟩ printed.reads printed.shells (Poetry.Agenda.belt_p cal k x) order i n
      (label (dock P K n)) kd pins hn).2 field
  rw [← eqn]
  exact (exact_heat printed i (mingle field pins) order).1
end YM.Integration.FVA1Physical.MixedResets

