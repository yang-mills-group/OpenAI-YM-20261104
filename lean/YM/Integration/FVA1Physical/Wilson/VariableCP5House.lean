import YM.QuadraticLocal.Tariff.Checkpoint5

/-! Choose the physical jet order independently of the scale's support exponent.
All CP5 conditional densities, forced ledgers, budgets, calendar, roofs and
signed horizon estimates are bought together on one trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore.Treehouse
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Integration.LocalComparison VowsR QuadraticLocal.Mentor
open Locator Rebirth Scholar Affinity RG3 RG3.Annuncia Oak Boot Boot.Marquee
open MintClock Moonlight
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (g:G.Simple)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
variable {φ:ℕ→ℕ} (C:LawScroll G φ) (Q0:Offices.Books D R.rolls Q φ)
variable (ZΘ:ℝ) (Qa:Mentor.Forecast D R.rolls Q φ Q0)
structure VariableHouse (profile:Orders) :Prop where
    stage : WithStage R.metals.p profile
    price : R.family.path.levels.clock.kernel.penalty= ZΘ
    stamps : Spill.Raffle.Warm G D R.alloy.delay φ
    admission : WheelP.Certified R.alloy R.kit
    freshness : Scholar.Renewal R.rolls D Q R.alloy.delay
    calendar : MintClock.Regency D R.rolls Q R.kit.target φ Q0 Qa R.alloy.delay
    licence : Oak.Tutoring.Quarterly R D Q C Q0 Qa
    rough : MintClock.Pavilion.Purchased D R.rolls Q R.kit.target φ Q0 R.alloy.delay
    quantity : MintClock.Pavilion.Quantity.Park R.rolls R.alloy.delay
    across (k:ℕ) (Sj:Syl.School k)(x₀ d₀ q qV M1 qx ℓq :ℕ)(Hc ε zP ηz δ₁ ℓ ℓ':ℝ) (he:0≤Hc) (hp0:0<ε)(hV:ε ≤ 1/8)(hf:4*ε≤ δ₁)(hd:0<ℓ')(hℓ:0≤ℓ)(hη:ηz≤1/4)(hη':0<ηz)(h2: 2≤Sj.order)(hzp:zP<1/2):
       ∀ᶠ b:ℕ in atTop,∀ m≤b,PaceR.Close R ℓq ℓ m b → Visitor R D Q Q0 Sj Qa x₀ d₀ ε Hc zP ηz δ₁ qx m b ∧ Moonlight.Orbit.Licence (k:=k) R D Q Q0 rough ( Boot.Marquee.rook R ) q qV M1 m b ℓ'

include g in
theorem variable_university (profile:Orders) (draft:Draft profile)
    (cover:∀ i,100 ≤ profile.supportExp i) (split:MintClock.splits ≤ φ) (positive:0<ZΘ):
    ∃ (R:Run G) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
      (Q:D.Tab R.rolls) (Q0:Offices.Books D R.rolls Q φ) (Qa:Mentor.Forecast D R.rolls Q φ Q0),
      VariableHouse R D Q C Q0 ZΘ Qa profile:=by
  let flow:=both G φ C (both G φ (Spill.Walking.short G φ) (both G φ
    (both G φ (Pavilion.scroll (ψ:=φ) G) (Pavilion.Quantity.renter (ψ:=φ) G)) (Scholar.cycles (ψ:=φ) G)))
  obtain ⟨R,D,Q,Q0,Qa,hstage,hprice,stamps,admission,calendar,cycle⟩:=
    Tracks.borscht g flow profile draft cover split ZΘ positive
  let t:=cycle.employed
  let openC:Chamber C R.kit D Q Q0:={t with obligation:=t.obligation.1}
  let school:Tutoring.Quarterly R D Q C Q0 Qa:={cycle with employed:=openC}
  let renew:=t.obligation.2.2.2
  let rough:=t.obligation.2.2.1.1
  let park:=t.obligation.2.2.1.2
  refine ⟨R,D,Q,Q0,Qa,hstage,hprice,stamps,admission,renew,calendar,school,rough,park,?_⟩
  intro k Sj x d q qV M1 qx ℓq Hc ε zP ηz δ₁ ℓ ℓ' he hp0 he0 hf hd hℓ hη hη' h2 hzp
  exact Boot.Marquee.night R g D Q C Q0 Sj Qa school stamps x ℓq d ε ℓ hp0 he0 hℓ renew calendar
    admission Hc zP ηz δ₁ qx hη hf rough park (Boot.Marquee.rook R) h2 hzp he hη' q qV M1 ℓ' hd

def widenedOrders (capacity:ℕ→ℕ):Orders :=
  {Tracks.readings with jets:=fun j=>6+j+capacity j}

theorem widened_draft (capacity:ℕ→ℕ) (mono:Monotone capacity) : Draft (widenedOrders capacity) :=
  {Tracks.preview.1 with mono:=fun _ _ h=>Nat.add_le_add (Nat.add_le_add_left h 6) (mono h)
                         k:=fun i=>(Tracks.preview.1.k i).trans (Nat.le_add_right ..)}

end YM.QuadraticLocal.Advent.Sycamore.Treehouse
