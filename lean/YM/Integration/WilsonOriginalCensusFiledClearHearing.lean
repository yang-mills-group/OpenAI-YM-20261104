import YM.Integration.WilsonOriginalCensusFiledHardWallet
import YM.Integration.WilsonOriginalCensusFiledClearCredit

/-! Withdraw the occupied part of the same original filed post at a clear nominated field, with its own wallet paid. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledClearHearing
open Filter MeasureTheory Multi
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open MeasureTheory Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m   ≤   i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {S:V→ℝ}{a:ℕ}{submitted:Config G (R.family.side (i+1) per)→Poly (Stock.census V)}
  (pub:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted)

local notation "P₀" => pub.post
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi (P₀).op (P₀).lesson ahead pub.order pub.shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi (P₀).op (P₀).lesson ahead pub.order pub.shelf
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (pub.order+pub.shelf+1) (P₀).op.count (width) (fig).limitC G*
  ((fig).produce (R.family.path.levels.clock.op i per).ratio.count*(P₀).cost)
local notation "H" => R.family.path.levels.clock.hatBeta i
local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num:0<(1:ℝ))
local notation "marks" => Stock.census V
local notation "testers" => WilsonOriginalMixedBlockRows.room V
local notation "noneYet" => fun _:V=>(⊥:Submodule ℝ ℂ)

open WilsonOriginalOccupiedCorridor WilsonCapturedPrimarySoftPartition
local notation "homes" => ((P₀).passport.coarser (R.family.path.levels.clock.op i per).ratio).origin
local notation "rank" s:max Δ:max => 2*(s).val.card+(a+∑v∈(s).val,Δ v)

/-- Both ages and the optical span are fixed before the physical cutoff and the period. -/
structure Opening (simple:G.Simple)(n drift debt power:ℕ)(np:0 < n)(load:∀t:(marks).Mode,t.val.card ≤ n)
    (C η:ℝ)(cp:0 ≤ C)(ep:0 < η)(b i:ℕ):Prop where
  base : (WilsonOriginalOccupiedOptical.original R simple (marks) n drift debt power np load C η cp ep).choose ≤ b
  age : (eventually_atTop.mp (WilsonOriginalOccupiedOptical.original R simple (marks) n drift debt power np load C η cp ep).choose_spec).choose ≤ i-1
  span : ((i-b:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i))^drift

theorem opening (simple:G.Simple)(n drift debt power:ℕ)(np:0 < n)(load:∀t:(marks).Mode,t.val.card ≤ n)
    (C η:ℝ)(cp:0 ≤ C)(ep:0 < η):
    ∃ tail start:ℕ,∀ b i,tail ≤ b → start ≤ i →
    ((i-b:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i))^drift →
    Opening R simple n drift debt power np load C η cp ep b i:=by
  let menu:=WilsonOriginalOccupiedOptical.original R simple (marks) n drift debt power np load C η cp ep
  exact ⟨menu.choose,(eventually_atTop.mp menu.choose_spec).choose+1,fun _ _ hb hi span=>⟨hb,by omega,span⟩⟩

include cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass:Pass D Q R.alloy R.kit)(hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:pub.shelf ≤ R.alloy.B.a.clock.J i)(load:(P₀).op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ i)(more:ready (P₀).op.count ≤ i)
    (wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ i)
    (neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i)
    (ticket:TicketP R.alloy R.kit D Q){b:ℕ}(mb:m ≤ b)(bi:b ≤ i)(pos:0 < i)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,pub.grades v)+1 ≤ pole)
    (hardFloor:6*pub.seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ pub.order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(rented:ε*g^q ≤ 1)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple (P₀).op.count q pub.order k deep aged ep ≤ i)
    (s:(marks).Mode)(charges:V→ℕ)(nn:∀v,0≤S v)(wages:∀v,S v ≤ H^(charges v))

    (n drift p:ℕ)(np:0 < n)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)(C η:ℝ)(cp:0 ≤ C)(ep₀:0 < η)
    (optics:Opening R simple n drift (rank s charges) p np load_ok C η cp ep₀ b i)
    (W:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold W=∅):
    ‖WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) bi Ψ (pub.appointment.row pub.x) s W‖ ≤
    (η*(Pert.Asymptotics.regulatorRun R.family N per i)^p)*(shards (marks) s).card:=by
  have restored:=WilsonOriginalCensusFiledHardWallet.original R hk D Q π Γ Ψ books hi cut ahead pub
    simple course pass hospital narrow load one more q rented wide neighbor s charges nn wages
  have earned:=WilsonOriginalCensusFiledClearCredit.original R hk D Q π Γ Ψ books hi cut ahead (testers)
    (noneYet) pub.grades pub.order pub.shelf pub.seats pub.law (P₀) _ pub.appointment simple n drift (rank s charges) p
    load_ok np C η cp ep₀ way course ticket mb bi pos optics.base optics.age optics.span
    pole q sourced hardFloor deep aged ep opened pub.x s W clear
  exact earned.2 restored

end YM.Integration.WilsonOriginalCensusFiledClearHearing
end
