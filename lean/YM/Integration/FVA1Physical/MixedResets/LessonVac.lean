import YM.Integration.FVA1Physical.MixedResets.Lesson
import YM.QuadraticLocal.Rebirth.Roots

/-!
# Subtraction of unmarked payload: working fields and kinetic reset

Identify the complete unmarked publisher with the same formal cover prescription.
No identification between working and preposterior `β`; the latter is to be compared
using `Rector.Ledger.sold` on the native measured clock, obtained *on this course*.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Tree Function Filter Finset MeasureTheory Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent
open Comparison.RG02 Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ}
variable (pay : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : pay.Tab R.rolls)
  (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (hi : m ≤ i) (L : Oak.Lesson (N:=N) R J pay Q π Γ hi)
  {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ) (cut : i < N)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "xStage" => R.alloy.B.a.clock.J (i+1)
local notation "yStage" => R.alloy.B.a.clock.J i
local notation "Y" => (RunFormalChain.fromRun R)
local notation "C" => Route.step R i n
local notation "p₀" => (Burn.horizon k+2)
local notation "T" => Step.tape p₀
local notation "income" => litP pay R.alloy Q (show Burn.horizon k+2≤ R.alloy.B.a.clock.J i from J.trans (R.alloy.B.a.fits.mono hi)) L.entry
local notation "cSide" => R.family.side i n
local notation "rep" j:max => R.family.path.rep N n j
local notation "f" => coverAction

include cut L

theorem lesson_vacuum (r : ℕ) (hr : r ≤ Burn.horizon k+2)
    (z : rule (Coarse G) (R.family.side i n)) :
    Route.vacuum R N p₀ (π (i+1)) r z = ↑(vista (income).presence L.entry r cSide z) := by
  unfold Route.vacuum
  rw [lesson_action R pay Q J π Γ hi L cut, lesson_clip R cut, L.ticket, lesson_patch R]
  -- defeq kernel
  rw [show (Route.step R i n).kernel = R.metals.p.kernel from R.alloy.B.valid.kernel]
  exact (cover_vacuum_law income L.entry z hr).1.symm

abbrev Route.calibrator : Adjacent.Caliber := Rebirth.caliber (Γ i) (Oak.grade0 R J pay Q π Γ hi L)
local notation "Cal" => Route.calibrator R pay Q J π Γ hi L
local notation "B" j:max => ( Faith.Spirit.suction (n:=R.family.side j n) (Pace.grouping 0 (π j) T ((rep j).clip) ((rep j).path)) )

set_option quotPrecheck false
local notation "recov" j:max => Route.vacuum R N p₀ (π (i+1)) j

variable {V : Type} [Fintype V] [DecidableEq V] {I : Marker.Census V} (U : Bulk.Colors I G (R.family.side (i+1) n))
    (F : Forest ((Route.step R i n).ratio)) (t : (Route.step R i n).Choices)
    (pledge : Oak.Rector.Ledger R J pay Q π Γ Ψ hi cut L U F t)

/-- Discard only a common field-independent scalar in the **vacuum**. -/
structure VacuumStep : Prop where
  post : ∃ a : ℕ → ℝ, ∀ r ≤ p₀,
    ( B i ) r = Adjacent.born (fun j (z : rule (Coarse G) cSide) => Route.vacuum R N p₀ (π (i+1)) j z + (a j : ℂ)) ((Cal).back p₀) 0 p₀ r ∧
    Adjacent.born (B i) ((Cal).direct p₀) 0 p₀ r = fun z => (Route.vacuum R N p₀ (π (i+1)) r z + (a r : ℂ))
  kinetics : Γ i 0=0 ∧ Γ i 1=0 ∧ Γ i 2=R.alloy.B.kin.alpha N i
  reads : ( Ψ i ).p.threshold^2*|(Ψ i).beta-Wheel.now (Γ i) p₀ (Ψ (i+1)).beta| ≤ Rosary.Repair.PostP.θ2 G (R.metals.p.profile yStage) ((σ).clock.hatBeta i) k
  forecast : Wheel.now (Γ i) p₀ (Ψ (i+1)).beta = (Ψ (i+1)).beta * (Cal).tariff p₀ (Route.coupling R N (i+1) n)
  couplings : (Ψ i).beta = (rep i).beta ∧ (Ψ (i+1)).beta = (rep (i+1)).beta

include pledge conc
set_option maxHeartbeats 200000
lemma vacuum_step : VacuumStep R pay Q J π Γ hi L (Ψ:=Ψ) := by
  have lo := later R π Γ Ψ conc hi cut.le
  have up := later R π Γ Ψ conc (Nat.le_succ_of_le hi) cut
  let src := Faith.Spirit.suction (n:= cSide) (Pace.grouping (Γ i) (π i) T ((rep i).clip) ((rep i).path))
  let frame := avatar R π Γ Ψ conc hi cut.le
  have hp : (Ψ i).path = (rep i).path := frame.path
  have hc : (Ψ i).clip = (rep i).clip := frame.clip
  have hu : (Ψ (i+1)).beta = (rep (i+1)).beta := up.beta
  have hfor := pledge.forecast
  change Wheel.now (Γ i) p₀ (Ψ (i+1)).beta = (Ψ (i+1)).beta * (Cal).tariff p₀ (Coat.gStep (Ψ (i+1)).beta) at hfor
  refine ⟨?_, Oak.Rector.refocus R J pay Q π Γ hi L, pledge.sold, ?_, lo.beta, up.beta⟩
  · have eqs (j : ℕ) (h : j ≤ Burn.horizon k+2) :
        ( B i ) j = Adjacent.born src ((Cal).back p₀) 0 p₀ j ∧
        src j = Adjacent.born (B i) ((Cal).direct p₀) 0 p₀ j ∧
        ∃ a : ℝ, ∀ z, src j z = Route.vacuum R N p₀ (π (i+1)) j z + (a : ℂ) := by
      dsimp only [src]
      rw [← hp, ← hc]
      obtain ⟨he,hg,a,cost⟩ := pledge.newborn j h
      refine ⟨hg,he.symm,a, fun z =>?_⟩
      rw [lesson_vacuum R pay Q J π Γ hi L cut j h]
      exact (congr_fun cost z).trans (Complex.ofReal_add ..)
    choose a ha using fun j : Fin (p₀+1) => (eqs j.val (Nat.le_of_lt_succ j.prop)).2.2
    let b (j : ℕ) := if h : j ≤ p₀ then a ⟨j,Nat.lt_succ_of_le h⟩ else 0
    have cost (r : ℕ) (hr : r ≤ p₀) (z) : src r z = Route.vacuum R N p₀ (π (i+1)) r z + (b r : ℂ) := by
      rw [show b r = a ⟨r,Nat.lt_succ_of_le hr⟩ from dif_pos hr]
      exact ha ⟨r,Nat.lt_succ_of_le hr⟩ z
    exact ⟨b, fun r hr => ⟨(eqs r hr).1.trans (congr_fun (born_through Cal p₀ p₀ cost) r),
      (eqs r hr).2.1.symm.trans (funext (cost r hr))⟩⟩
  unfold Route.coupling
  rw [← hu, hfor]
end YM.Integration.FVA1Physical.MixedResets
