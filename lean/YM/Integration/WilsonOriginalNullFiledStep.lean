import YM.Integration.WilsonOriginalNullBooked

/-! Emit the actual measured lower primary and a projection-null lower source
on the very same original Wilson history. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFiledStep
open YM.Integration.WilsonMeasuredOwnerReserve
open Labels Source WilsonPhysicalMarkedDefect.RegularProjection
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Pert.Asymptotics Extra.Histories Trace.Physical.GermGraph Trace.Physical
open RG16 WilsonMeasuredCoefficientTransport WilsonMeasuredOwnerAppointments
open Progress.DirectedRecipe QuadraticLocal.Tint

local notation "incoming" => Ψ (i+1)
local notation "κ₁" => LocalComparison.forcedDivisor R.family (i+1)
local notation "κ₀" => LocalComparison.forcedDivisor R.family i
local notation "cash" => R.family.path.levels.clock.forcedAllowance (i+1)
local notation "labels₁" => Stock.census (Fin 1)
local notation "temperature" => R.alloy.B.a.clock.hatBeta (i+1)

local notation "hc" => R.family.path.rep N per (i+1)
local notation "g₁" => Coat.gStep (hc).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "L₀" => ((R.family.S.block i).val:ℝ)
variable (origin:Site (R.family.side (i+1) per))
local notation "coarse" => (R.family.path.levels.clock.op i per).ratio.parent origin
variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "scaleCost" => WilsonMeasuredRankedResidual.sourceCost R rank
local notation "wrap" => WilsonMeasuredRankedPrimaryBudget.wrap (F₀) Y₀



open Extra.Histories Extra.Histories.Relay Next.Foundations
open WilsonPhysicalMarkedDefect.RegularProjection
/-- The fine and coarse presentations, dependency on origin, original forced
divisor and normalized log coordinate are all part of this transition. -/
def Filed (C:Family G) (d N p j:ℕ) (W:∀ k,Rep G (C.side k p)) (y:Site (C.side (j+1) p)) (ε:ℝ) : Prop :=
  let A:=C.params
  let F:=C.labels.level d
  let S:=C.localSection d
  let o:=(C.path.levels.clock.op j p).ratio.parent y
  let L:ℝ:=(C.S.block j).val
  ∀ (h:Coefficient F (C.side (j+1) p)) (B:ℝ),
    h.Format y A (W (j+1)) → h.remBound y (W (j+1)) (LocalComparison.forcedDivisor C (j+1)) B →
    Germ.projection F A (W (j+1)).p.threshold y h=0 →
    ∃ (v:Coefficient F (C.side j p)) (α:F.Coeff),v.Format o A (W j) ∧
      v.remBound o (W j) (LocalComparison.forcedDivisor C j) (L^(-(1/8:ℝ))*B) ∧
      Germ.projection F A (W j).p.threshold o v=0 ∧ L^(1/8:ℝ)*F.coeffSize α ≤ ε*B ∧
      GermGraph.transition (C:=C) d N p j (h.density y S (W (j+1))) =
        v.density o S (W j)+(primary o α).density o S (W j)

include P in
/-- Engineering-restored original Wilson null gate at every displaced source. The two actual hard carriers and all induced regular and forced outputs are retained. -/
theorem original (ticket:V) (live:i<N) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (size:seats ≤ Burn.horizon k+2)
    (way:WayStation R.kit)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (q:ℕ) (deep:2*(q+4+1)+8≤order) (aged:q+4+4≤3*k+2) (accuracy:2*rank+5≤q)
    (eligible:Ready R simple rank q k order shelf M slow prepared accuracy deep aged i)
    (step : TicketP R.alloy R.kit D Q)
    (ε:ℝ) (ep:0 < ε) (calendar:WilsonOriginalNullBooked.Date R rank simple M q ε i) :
    Filed R.family rank N per i Ψ origin ε := by
  intro h B form fund null
  have minp:0 < min ε 1 := lt_min ep zero_lt_one
  obtain ⟨z,u,shape,paid,gross,rate,read⟩:=WilsonOriginalNullStrongGate.original R hk D Q π Γ Ψ
    books ahead actors pieces grades order shelf seats floor physical P origin rank ticket live simple course
    scroll chamber pass hospital size way M slow prepared fixed q deep aged accuracy eligible step
    (min ε 1) minp calendar.reserve (calendar.compulsory N per live) h B form fund null
  have point:=(QuadraticLocal.Advent.later R π Γ Ψ course floor live.le).truep.point
  have dword:rank ≤ (Ψ i).p.order:=by rw [point];exact calendar.reserve.ordinary.lower.2.2.1
  have dpoly:rank ≤ (Ψ i).p.power:=by rw [point];exact calendar.reserve.ordinary.lower.2.2.2.1
  obtain ⟨shaped,fee,zero,_,head,split⟩:=(eventually_atTop.mp
    (WilsonOriginalNullLanding.local_section R rank simple)).choose_spec i calendar.landing
    per (Ψ i) point coarse z shape paid gross dword dpoly (by rw [point];exact fixed)
  let α:=Germ.projection F₀ Y₀ (Ψ i).p.threshold coarse z
  let v:=WilsonMeasuredSectionCorrection.subtract F₀ z α
  have u0:=rem_nonneg paid
  have B0:=rem_nonneg fund
  have s0:0≤(R.family.path.levels.params i).columns:=le_trans zero_le_one (R.family.path.levels.params i).columns_ge
  have Lp:0 < L₀:=zero_lt_one.trans_le (GermGraph.factor_positive R.family i).le
  have r0:=Real.rpow_nonneg Lp.le (-(1/8:ℝ))
  have two : 2*u ≤ (2+4*(R.family.path.levels.params i).columns)*u:=by nlinarith only [mul_nonneg s0 u0]
  have b' := rate.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right ε 1) r0) B0).trans_eq
    (by rw [one_mul]))
  have ub : u ≤ L₀^(-(1/8:ℝ))*B:= (show u≤2*u by linarith only [u0]).trans (two.trans b')
  refine ⟨v,α,shaped,rem_mono fee ub,zero,?_,read.symm.trans split⟩
  calc
    L₀^(1/8:ℝ)*(F₀).coeffSize α ≤ L₀^(1/8:ℝ)*((min ε 1*L₀^(-(1/8:ℝ)))*B) :=
      mul_le_mul_of_nonneg_left (head.trans (two.trans rate)) (Real.rpow_nonneg Lp.le _)
    _ = min ε 1*B := by rw [Real.rpow_neg Lp.le];field_simp
    _ ≤ ε*B := mul_le_mul_of_nonneg_right (min_le_left ε 1) B0

end YM.Integration.WilsonOriginalNullFiledStep
