import YM.Integration.WilsonOriginalCensusFiledHardWallet
import YM.Integration.WilsonOriginalCensusFiledHousing

/-! Withdraw the occupied part of the same original filed post at either flat, with its own wallet paid. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledHardHearing
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
include cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass:Pass D Q R.alloy R.kit)(hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:pub.shelf ≤ R.alloy.B.a.clock.J i)(load:(P₀).op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ i)(more:ready (P₀).op.count ≤ i)
    (wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ i)
    (neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i)
    (ticket:TicketP R.alloy R.kit D Q){u b:ℕ}(floor:m ≤ u)(ub:u ≤ b)(bc : b < i)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,pub.grades v)+1 ≤ pole)
    (hardFloor:6*pub.seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ pub.order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(rented:ε*g^q ≤ 1)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple (P₀).op.count q pub.order k deep aged ep ≤ i)
    (s:(marks).Mode)(charges:V→ℕ)(nn:∀v,0≤S v)(wages:∀v,S v ≤ H^(charges v))
    (n:ℕ)(np:0<n)(stage:∀l,b ≤ l → n ≤ R.alloy.B.a.clock.J l)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)
    (cap:∀l,b ≤ l → LocalComparison.forcedDivisor R.family l ≤ 1)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(home:center∈Z)
    (resident:∀v∈s.val,sites R (homes) bc.le v∈Z)
    (size d p:ℕ)(C e:ℝ)(cp:0≤C)(ep₀:0<e)
    (enclosed:coverNumber (Ψ b).p.B Z ≤ size)(support:(Ψ b).p.supportExponent=100)
    (room:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple 0 (by norm_num:0<(1:ℝ)))).choose ≤ b)
    (late:(eventually_atTop.mp (WilsonOriginalOccupiedOpticalRate.original R simple n d (rank s charges) p C cp e ep₀)).choose ≤ i-1)
    (span:((i-b:ℕ):ℝ)≤C*(1+Real.log H)^d):
    ∀{v:ℕ},u ≤ v → ∀(vb:v ≤ b),‖WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) (vb.trans bc.le)
      Ψ (pub.appointment.row pub.x) s (1:Config G (R.family.side v per))‖ ≤
        (e*(Pert.Asymptotics.regulatorRun R.family N per i)^p)*WilsonOriginalCensusFiledHousing.fare s size:=by
  intro v uv vb
  let debt:=(8*Ω^(P₀).op.count)*(P₀).rent+ε*g^q
  let src:=Stoop.radius (P₀).w (max 1 (cash+debt))
  let fee:=Poly.toll (wallet R src bc.le) s
  let gain:=H^(rank s charges)*Poly.toll src s
  let tariff:=WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card
  have restored:1≤gain:=WilsonOriginalCensusFiledHardWallet.original R hk D Q π Γ Ψ books hi cut ahead pub
    simple course pass hospital narrow load one more q rented wide neighbor s charges nn wages
  have charged:=(WilsonOriginalCensusFiledOpticalCredit.original R hk D Q π Γ Ψ books hi cut ahead (testers)
    (noneYet) pub.grades pub.order pub.shelf pub.seats pub.law (P₀) _ pub.appointment simple way course ticket
    floor ub bc fixed capture pole q sourced hardFloor deep aged ep opened pub.x s n np stage load_ok cap Z center home
    resident d (rank s charges) p C e cp ep₀ late span uv vb).1
  have fresh:∀v,0<src v:=fun v=>div_pos ((P₀).salary.positive v) (zero_lt_one.trans_le (le_max_left ..))
  have f0:0≤fee:=(Poly.worth (positive R src fresh bc.le) s).le
  have paid:fee≤gain:=(WilsonOriginalCensusFiledHousing.shrinking R bc.le src fresh s).trans
    (le_mul_of_one_le_left (Poly.worth fresh s).le (one_le_pow₀ (R.family.path.levels.fits.delayed _).le))
  have q0:0≤tariff:=by
    dsimp only [tariff,WilsonOriginalFlatOccupiedRate.bill,WilsonOriginalFlatOccupiedRate.roof]
    positivity
  have clock:=(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple 0 (by norm_num:0<(1:ℝ)))).choose_spec b room
  have cash₀:R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤ 1:=by simpa only [pow_zero,div_one] using clock.2
  exact WilsonOriginalCensusFiledHousing.clear restored paid f0 q0
    (WilsonOriginalCensusFiledHousing.enclosed (Ψ b).p Z size s.val.card support enclosed) cash₀
    (Nat.cast_nonneg _) (mul_nonneg ep₀.le (pow_nonneg (ActualRunKernelPackets.regulator_pos R N per i cut.le).le _)) charged

end YM.Integration.WilsonOriginalCensusFiledHardHearing
end
