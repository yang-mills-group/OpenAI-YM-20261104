import YM.Integration.WilsonOriginalNullBareBookHearing
import YM.Integration.WilsonOriginalNullBarePanel
import YM.Integration.WilsonCapturedPrimarySection
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonOriginalNullBareClean
import YM.Integration.WilsonOriginalNullBareGallery
import YM.QuadraticLocal.Advent
import YM.Integration.WilsonOlderFreshWordReversion
import YM.Integration.WilsonCenteredFullDensity

/-! The genuine uncut top word, on the complete clean-domain detector in the original vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareGerm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open Extra.Histories Extra.Trajectories Source Labels Push.Local Planned.GuardedAtom
open Comparison.RG02.Cumulants Ac
open WilsonOlderFreshGraphHostTarget WilsonCenteredFiledAtoms
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {m i N per k d:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i) (live:i+1 ≤ N) (school:Syl.School k)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {P:Earn.Passport (R.family.side (i+1) per) Unit} (A:Unit→Set ℂ)
  {J:Type} (M:J→Row P (Stock.census Unit) G (Wallet A))
local notation "U" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "κ" => forcedDivisor R.family (i+1)
local notation "β" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fire" => (Stock.census Unit).fire ()


open Trace.Physical.Germ Pert.Asymptotics WilsonCapturedPrimaryPaid
local notation "side" => R.family.side (i+1) per
local notation "μ" => (R.family.path.levels.params (i+1)).columns
local notation "η" => R.alloy.B.a.clock.forcedAllowance (i+1)
variable (e:ℕ)
local notation "Fr" => R.family.labels.level e
local notation "Y" => R.family.params
local notation "Sec" => R.family.localSection e
local notation "gs" => regulatorRun R.family ((i+1)+1) per ((i+1)+1)
include history live in
theorem original {τ c w fac θ:ℝ} {cut:ℕ} (simple:G.Simple)
    (post:Landed (d:=d) (N:=N) R hk D Q π Γ Ψ books hi school ahead A M τ c w cut)
    (wallet:Invoice.Supports (U).p fac ((U).p.supportExponent+2) (Coat.gStep (U).beta) σ₀ θ)
    (rank:R.t e ≤ i+1) (support:1 ≤ (U).p.supportExponent)
    (clock:WilsonCenteredCaptureClock.first R simple ≤ i+1)
    (wrapped:(eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i+1)
    (late:(eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple Fr Y Sec 3 0 1 le_rfl)).choose ≤ i+1)
    (small:(WilsonCapturedPrimaryDecoder.invoice Fr Y e)*gs^3*μ ≤ 1/2)
    (t:Wallet A) :
    let ap:=Invoice.price (U).p fac (school.order+school.horizon+1) school.pieces ((U).p.supportExponent+2) θ G
    let E:=ap*c
    let fee:=WilsonOlderSignedSingletonFare.fare (U).p Sec Y (fun _:Unit=>w) fire 1 {P.origin ()} 0
      E (κ*β^(-(cut:ℝ))) κ η μ
    let wrap:=WilsonCapturedPrimaryCoreBill.wrapFee Fr Y
    let gross:=2*(WilsonCapturedPrimaryDecoder.invoice Fr Y e*gs^3)*
      ((E/w)/gs^(grade 3 e 1)+μ*(wrap*fee)+fee)
    ∃ h:Coefficient Fr side, h.Format (P.origin ()) Y U ∧ h.remBound (P.origin ()) U κ fee ∧
      (∀ V,h.density (P.origin ()) Sec U V=((U).eval V:ℂ)*(Spill.Foundry.uncut M (Coat.gStep (U).beta) t V).part fire) ∧
      (Fr).coeffSize (projection Fr Y (U).p.threshold (P.origin ()) h) ≤ gross ∧
      (Fr).coeffSize h.x ≤ gross+wrap*fee :=by
  intro ap E fee wrap gross
  have ing:=(history.1.walk (i+1) (Nat.le_succ_of_le hi) live).truep
  have read:=WilsonCapturedPrimarySection.original R rank U ing.point
  obtain ⟨div,non,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec (i+1) clock
  have room':hitWidth (U).p*η ≤ 1:=by rw [ing.point];exact room
  let raw:=fun (V:Config G side)=>(Spill.Foundry.uncut M (Coat.gStep (U).beta) t V).part fire
  have bank:Store U Sec Y (P.origin ()) κ fee (fun V=>((U).eval V:ℂ)*raw V):=by
    simpa only [one_mul] using WilsonOriginalNullBarePost.issued R hk D Q π Γ Ψ history books
      hi live school ahead A M post wallet ing.valid div non room' Sec Y read.1 t 1
  have heard:∀ V:Config G side, flags (U).p.threshold V=∅ → ‖raw V‖ ≤ E/w:=by
    intro V hv
    simpa only [one_mul,norm_one] using WilsonOriginalNullBareBookHearing.original R hk D Q π Γ Ψ
      books hi school ahead A M post wallet t 1 V hv
  have pos:0 ≤ E/w:=(norm_nonneg (raw 1)).trans (heard 1 (UVNext.CouplingReset.flags_one (U).p))
  exact WilsonOriginalNullBarePanel.original R Fr Y Sec simple 3 wrapped late U ing.point
    support read.2 (P.origin ()) read.1 raw bank pos heard small
end YM.Integration.WilsonOriginalNullBareGerm
