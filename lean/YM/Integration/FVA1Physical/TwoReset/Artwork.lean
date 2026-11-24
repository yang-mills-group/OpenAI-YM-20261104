import YM.Integration.FVA1Physical.TwoReset.RepeatedAtoms
import YM.QuadraticLocal.Fk.Pulse

/-! Identify CP5 artwork against RG02.Bulk.Fk on arbitrary periods, with ONE
quantitative seam rate shared by all clubs. Frame, patch and stage are physical;
the incoming unmarked extra action is the published layout (starts at order three);
retain the complete stochastic numerator and denominator of that prescription through
this order. In this comparison the period n can be an arbitrary cover of the later
physical support period and `b` any spacing of the marks on it. -/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Echo QuadraticLocal.Mentor QuadraticLocal.Earn RemainderComparison
open Seedlings Offices Cruise
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open Laurent Stationary AllOrder.Ink AllOrder.Ink.Money Comparison.RG02 Kinetic.Port Pane
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {X : Metals G}
variable (R : Roots (G:=G) X.p.profile X.K X.p.kernel) (D : Rolls X.p) (Q : R.Tab D)
variable (A : Alloy X D) (φ : ℕ→ℕ) (K0 : Offices.Books R D Q φ)
variable {m : ℕ}
local notation "x" => A.B.a.clock.J (m+1)
local notation "y" => A.B.a.clock.J m
variable (o : Opportunity (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (E : Epoch R D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) o)
    (T : Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon E.vac))
local notation "baseHeight" => Burn.horizon E.vac

variable {ι V α : Type} [Fintype V] [DecidableEq V]
variable {c f : Side}
variable (u : f.val = c.val * (A.B.a.S.block m).val)
variable {J : Passport f V} {S : Marker.Census V} (M : ι → Row J S G α) (C : Club M)
variable (p : ℕ)
variable (v : Voter M (QuadraticLocal.Poetry.Agenda.seed R φ (Burn.horizon E.vac) (A.B.a.clock.J (m+1)))
    p o.count o.stage E.vac (A.B.a.clock.J m))
local notation "N" => Cruise.publish R D Q A φ K0 o E u M p v T
local notation "keys" => Club.Keys M C
local notation "loan₁" => (fun i: Club.Keys M C => (Club.troops M C i).lamp)
local notation "ticket₁" => Cruise.ticket R D A φ o E M C p v
local notation "rules₁" => Cruise.rules R D A φ o E u M C p v
local notation "art" => Mentor.artifact R D A φ o E ticket₁ rules₁ T
local notation "ledger" => (K0.lore x y o E ticket₁)
local notation "angle" => (ticket₁).val.angle
local notation "epoch" => Epoch.data R D Q o E
local notation "rate" => Wharf.rate (Wharf.title D R x y Q φ K0)
  (Wharf.upper D R x y Q φ K0) T.self.paid
local notation "σ" => Poetry.Agenda.poll R baseHeight x

variable {n B : Side}
variable (hB : B.val = n.val * (A.B.a.S.block m).val)
local notation "L" => Pane.panel A m hB
variable (c₀ : Clip) (u₀ : PathData G) (T' : Layout G)
    (Y : Bulk.Kernel (Pane.panel A m hB) c₀ u₀ X.O)
    (F : Forest (Pane.panel A m hB).ratio) (z : (Pane.panel A m hB).Choices)
    (ht : T' = T.extra) (hP : u₀ = T.self.north)
    (hC : c₀ = (X.p.profile (A.B.a.clock.J (m+1))).clip) (hl : Bid.Larger (G:=G) (Pane.panel A m hB))

/-- Unit Fk response from repeated (or just relocated) rows. The pattern b weights
fine sites with the same local addresses *in their subdivision blocks*. -/
abbrev response {G : Gauge} {V α ι : Type} [DecidableEq V] {n B f : Side}
    {J : Passport f V} {S : Marker.Census V} (M : ι → Row J S G α) (C : Club M)
    (U : Layout G) (Ages : Finset Age)
    {LK : StepData n B} {p : Clip} {P : PathData G} {O : ChartRatio G}
    (Y : Bulk.Kernel LK p P O) (F : Forest LK.ratio) (z : LK.Choices)
    (seat : Club.Keys M C → Site n → Site B)
    (a : Link G n) (b : rule (Club.Keys M C) n) (r i : ℕ) : ℂ :=
  let W := Focus.census (Club.Keys M C)
  let V₁ := Balcony.displayC (fun i:Club.Keys M C=> (Club.troops M C i).lamp)
    (fun i:Club.Keys M C=> (Club.troops M C i).atom) seat U Ages b
  (Order.observe W r (Order.logMarked (Bulk.Fk Y F z V₁ (Stationary.arm G n 1 a) r)) i).part
    (Focus.onto (univ:Finset (Club.Keys M C)))

local notation "seat₁" => Echo.Sara.seat (Mural.sheet X.p D E.wants) L
  (Plateau.Line.patch_here A hB) (rules₁).lodger

include ht hP hC hl v
-- Reuse the *same* Publication at the larger period. No new construction with
-- constants depending on cover ratio is required. Compare also before resolving
-- neighbourhoods or deciding whether these are wrapping vertices.
theorem artwork (a : Link G n) (b : rule (Club.Keys M C) n) (i : ℕ) (hi : i ≤ p) :
    ‖response M C T' (Step.tape (Burn.horizon E.vac+2)) Y F z seat₁ a b p i -
      Complex.ofReal (production ((N).news C) a b i)‖ ≤
        (rate n * dearth σ n) * (1 + ‖mingle a b‖)^(i+Press.toll M C+2) := by
  haveI := E.head
  let book := Publication.reads D R x y E.wants φ loan₁ epoch art i n
  let Lout := Publication.report D R x y E.wants φ loan₁ angle epoch ledger art i n
  have heq : response M C T' (Step.tape (baseHeight+2)) Y F z seat₁ a b p i =
      Complex.ofReal (book (mingle a b)) :=
    Publication.identifies D R x y E.wants φ loan₁ angle epoch ledger art hi L
      (Plateau.Line.patch_here A hB) A.B.valid.kernel hl c₀ u₀ T' hC hP ht Y F z a b
  let U : Port.Cashpoint R D x y :=
    ⟨o,E,ticket₁,(show Fin ((ticket₁).val.order+1) from ⟨i,Nat.lt_succ_of_le hi⟩)⟩
  have Hp : Prices (Poetry.Agenda.guard loan₁ univ i) (rate n * dearth σ n) (book-Lout) :=
    (Wharf.warranty D R x y Q φ K0 U).2.2 art n (Wheel.Ride.scope_complete L
      (Plateau.Line.patch_here A hB) A.B.valid.kernel hl)
  rw [Cruise.availability R D A φ o E M C p v i] at Hp
  let f₀ (j : ℕ) := ∑ x' : Site n, ∑' k, Poetry.Lantern.gleam
    (((ledger).atoms j art).leg k) x' b j i a
  have H : production ((N).news C) a b i = Lout (mingle a b) :=
    Fin.sum_univ_eq_sum_range f₀ (p+1)
  rw [heq,H,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact Hp.2.2 _
end YM.Integration.FVA1Physical.TwoReset
