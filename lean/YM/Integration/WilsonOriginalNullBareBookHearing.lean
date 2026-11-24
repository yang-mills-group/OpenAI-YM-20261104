import YM.Integration.WilsonOriginalNullBarePost
import YM.Integration.WilsonOriginalNullBareClean
import YM.Integration.WilsonOriginalNullBareGallery
import YM.QuadraticLocal.Advent
import YM.Integration.WilsonOlderFreshWordReversion
import YM.Integration.WilsonCenteredFullDensity

/-! The genuine uncut top word, on the complete clean-domain detector in the original vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareBookHearing
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

theorem original {τ c w fac θ:ℝ} {cut:ℕ}
    (post:Landed (d:=d) (N:=N) R hk D Q π Γ Ψ books hi school ahead A M τ c w cut)
    (wallet:Invoice.Supports (U).p fac ((U).p.supportExponent+2) (Coat.gStep (U).beta) σ₀ θ)
    (t:Wallet A) (z:ℂ) (V:Config G (R.family.side (i+1) per))
    (clear:flags (U).p.threshold V=∅) :
    let ap:=Invoice.price (U).p fac (school.order+school.horizon+1) school.pieces
      ((U).p.supportExponent+2) θ G
    ‖z*(Spill.Foundry.uncut M (Coat.gStep (U).beta) t V).part fire‖ ≤ ‖z‖*(ap*c/w) :=by
  obtain ⟨H,_,hw,hc,_,_,_,reg,hard⟩:=post
  have old:=reg ((U).p.supportExponent+2) (U).p.B
  rw [←hw] at old hard
  have cash:=Lamps.joinPaid
    (Scene.Armada.paid H.model H.w (fun _:Unit=>d) H.salary (U).p wallet) old
  have check:=WilsonOriginalNullBareClean.hearing (Tint.Patrol.picture H.model H.input)
    H.salary.positive (show 0≤(U).p.supportExponent+2 by linarith only [(U).p.exponent_pos])
    cash hard z t () V clear
  rw [H.represented t] at check
  let L:=Spill.Foundry.uncut M (Coat.gStep (U).beta) t V
  have hzero:=WilsonOlderFreshWordReversion.quiet M t (Coat.gStep (U).beta) V
  have one:(Poly.pass L).part fire=L.part fire:=by
    rw [←lamp () _ (Poly.pass_part L hzero),Comparison.RG02.Cumulants.connected_pass hzero]
  dsimp only [L] at one
  have hz:(↑((U).eval V):ℂ)≠0:=ProjectorNext.Equivariance.noFlagEval clear
  have mass:Poly.toll H.w fire=w:=by
    simp [hw,Poly.toll,Census.fire]
  simp only [Poly.part_smul,one,hc,H.capacity,add_zero,mass] at check
  rwa [← mul_assoc,mul_right_comm,mul_div_cancel_right₀ _ hz] at check
end YM.Integration.WilsonOriginalNullBareBookHearing
