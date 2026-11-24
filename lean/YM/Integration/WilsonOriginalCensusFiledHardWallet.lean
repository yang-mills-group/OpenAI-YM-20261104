import YM.Integration.WilsonOriginalCensusFiledOpticalCredit
import YM.Integration.WilsonOriginalFixedTestCensusOffer

/-! The genuine fresh filed salary restores the occupied radius at either receiver. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledHardWallet
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

private theorem bought {V:Type}[DecidableEq V]{J:Census V}(s:J.Mode){w:V→ℝ}{H₀ δ:ℝ}
    (wp:∀v,0<w v)(hp:0≤H₀)(pδ:0<δ)(bound:δ≤H₀^2)(k:ℕ)(prior:(Poly.toll w s)⁻¹≤H₀^k):
    1≤H₀^(2*s.val.card+k)*Poly.toll (Stoop.radius w δ) s:=by
  have id:(Poly.toll (Stoop.radius w δ) s)⁻¹=δ^s.val.card*(Poly.toll w s)⁻¹:=by
    simp only [Stoop.radius,Poly.toll,div_eq_inv_mul,Finset.prod_mul_distrib,Finset.prod_const,
      mul_inv,inv_pow,inv_inv]
  apply (inv_le_iff_one_le_mul₀ (Poly.worth (fun j=>div_pos (wp j) pδ) s)).mp
  change (Poly.toll (Stoop.radius w δ) s)⁻¹≤H₀^(2*s.val.card+k)
  rw [id,pow_add,pow_mul]
  exact mul_le_mul (pow_le_pow_left₀ pδ.le bound _) prior (inv_nonneg.mpr (Poly.worth wp s).le) (pow_nonneg (pow_nonneg hp _) _)

include cut in
theorem original (simple:G.Simple)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass:Pass D Q R.alloy R.kit)(hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:pub.shelf ≤ R.alloy.B.a.clock.J i)(load:(P₀).op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ i)(more:ready (P₀).op.count ≤ i)(q:ℕ){ε:ℝ}(small:ε*g^q ≤1)
    (wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ i)
    (neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i)
    (s:(marks).Mode)(charges:V→ℕ)(nn:∀v,0≤S v)(wages:∀v,S v≤H^(charges v)):
    let debt:=(8*Ω^(P₀).op.count)*(P₀).rent+ε*g^q
    let src:=Stoop.radius (P₀).w (max 1 (cash+debt))
    1 ≤ H^(2*s.val.card+(a+∑v∈s.val,charges v))*Poly.toll src s:=by
  intro debt src
  have filed:=WilsonOriginalOccupiedFiledFare.original R hk D Q π Γ Ψ course books hi cut ahead (testers)
    (noneYet) pub.grades pub.order pub.shelf pub.seats pub.law (P₀) pass hospital narrow load one more (P₀).small q ε small
  have roof:max 1 (cash+debt)≤10*R.alloy.B.a.clock.hatBeta (i+1):=
    (max_le_max_left 1 (le_max_left (cash+debt) (2*(1:ℝ)))).trans filed
  have hh:20≤H:=(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose_spec i wide
  have step:=(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec i neighbor
  have hp:0≤H:=zero_le_one.trans (R.alloy.B.a.fits.delayed i).le
  have cap:max 1 (cash+debt)≤H^2:=roof.trans <| calc
    _ ≤10*(2*H):=mul_le_mul_of_nonneg_left step (by norm_num)
    _ =20*H:=by ring
    _ ≤H^2:=by simpa only [pow_two] using mul_le_mul_of_nonneg_right hh hp
  exact bought s (P₀).salary.positive hp (zero_lt_one.trans_le (le_max_left ..)) cap _
    (WilsonOriginalFixedTestCensusOffer.occupied R hk D Q π Γ Ψ books hi ahead pub s charges nn wages)

end YM.Integration.WilsonOriginalCensusFiledHardWallet
end
