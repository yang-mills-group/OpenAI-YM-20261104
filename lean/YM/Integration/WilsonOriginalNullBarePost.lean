import YM.Integration.WilsonOlderFreshGraphHostTarget
import YM.Integration.WilsonOriginalNullBareGallery
import YM.QuadraticLocal.Advent
import YM.Integration.WilsonOlderFreshWordReversion
import YM.Integration.WilsonCenteredFullDensity

/-! The genuine uncut top word, including the original mask slips, on its deposited carrier. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBarePost
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
include history live in
theorem issued {τ c w fac θ μ ζ C Λ δ η:ℝ} {cut:ℕ}
    (post:Landed (d:=d) (N:=N) R hk D Q π Γ Ψ books hi school ahead A M τ c w cut)
    (wallet:Invoice.Supports (U).p fac ((U).p.supportExponent+2) (Coat.gStep (U).beta) σ₀ θ)
    (law:(U).Lawful ζ C Λ δ η) (div:0<κ) (non:0 ≤ η) (cap:hitWidth (U).p*η ≤ 1)
    {e:ℕ} {F:Frame G e} (S:SectionData F) (Y:Hol G) (read:Readable Y S (U).p (R.family.side (i+1) per) μ)
    (t:Wallet A) (z:ℂ) :
    let ap:=Invoice.price (U).p fac (school.order+school.horizon+1) school.pieces
      ((U).p.supportExponent+2) θ G
    Store U S Y (P.origin ()) κ (WilsonOlderSignedSingletonFare.fare (U).p S Y
      (fun _:Unit=>w) fire z {P.origin ()} 0 (ap*c) (κ*β^(-(cut:ℝ))) κ η μ)
      (fun V=>z*(((U).eval V:ℂ)*(Spill.Foundry.uncut M (Coat.gStep (U).beta) t V).part fire)) :=by
  obtain ⟨H,hp,hw,hc,_,_,_,reg,hard⟩:=post
  let slots:=QuadraticLocal.Advent.spare R π Γ Ψ history (Nat.le_succ_of_le hi) live
  let T:=Guard.Keeper.sufficient slots
  have reg' := reg ((U).p.supportExponent+2) (U).p.B
  rw [←hw] at reg' hard
  have result:=WilsonOriginalNullBareGallery.issued H.model H.input H.w
    (fun _:Unit=>d) H.salary wallet reg' hard T law div non cap S Y read () t z
  dsimp only at result ⊢
  obtain ⟨q,form,cost,value⟩:=result
  refine ⟨q,?_,?_,?_⟩
  · simpa only [hp] using form
  · simpa only [hp,hw,hc,H.capacity,add_zero] using cost
  · intro V
    have h:=value V
    rw [H.represented t] at h
    let L:=Spill.Foundry.uncut M (Coat.gStep (U).beta) t V
    have hzero:=WilsonOlderFreshWordReversion.quiet M t (Coat.gStep (U).beta) V
    have one : (Poly.pass L).part fire=L.part fire :=by
      rw [←lamp () _ (Poly.pass_part L hzero),Comparison.RG02.Cumulants.connected_pass hzero]
    dsimp only [L] at one
    simpa only [hp,Poly.part_smul,Pi.smul_apply,smul_eq_mul,one] using h
end YM.Integration.WilsonOriginalNullBarePost
