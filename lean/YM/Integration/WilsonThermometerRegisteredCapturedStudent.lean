/- The actual physical three-field student's one-mark income on its receiving date. -/
import YM.Integration.WilsonThermometerRegisteredCapturedMaterial
import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonThermometerCourseHearing
import YM.Integration.WilsonOlderFreshGraphPointWallet

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedStudent
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture

open WilsonThermometerRegisteredCapturedPace WilsonThermometerRegisteredCapturedUncut
open WilsonThermometerRegisteredCapturedSector WilsonThermometerRegisteredCapturedLedger
local notation "J"=>Stock.census (Fin 3)
local notation "C₁"=>Stock.census Unit
def disk (_:Unit):Set ℂ:={z | ‖z‖ ≤ 1}
def home {n:Side}(roots:Fin 3→Site n):ℕ:=∑v:Fin 3,(Earn.Cable.link 0 (roots v)).length
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple) {m i N per k:ℕ}
  (top:i+1 < N) (o:Positions (Fin 3) (R.family.side N per))
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls bank φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls bank φ books) (order shelf seats:ℕ)
local notation "ages"=>(fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
variable (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages
  order shelf seats (i+1) (Nat.le_succ_of_le hi) (offered R A simple top o))
local notation "sheet"=>R.family.path.levels.clock.op (i+1) per
local notation "student"=>Oak.student (n:=per) R hk D bank π Γ books (Nat.le_succ_of_le hi) P.op P.lesson ahead disks P.model order P.voter
local notation "fig"=>Oak.figureReal R hk D bank π Γ books (Nat.le_succ_of_le hi) P.op P.lesson ahead order shelf
local notation "oldG"=>Coat.gStep (Ψ (i+1+1)).beta
local notation "current"=>Coat.gStep (Ψ (i+1)).beta
local notation "seedWidth"=>Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "price"=> (fig).produce (sheet).ratio.count*P.cost
local notation "S"=>WilsonOlderFreshGraphPointWallet.point (0:Site (R.family.side (i+1) per))
local notation "roots"=>(P.passport.coarser (sheet).ratio).origin
local notation "roads"=>(fun v:Fin 3=>Earn.Cable.link (0:Site (R.family.side (i+1) per)) ((roots) v))
local notation "B"=> (Ψ (i+1)).p
def fare (Q:Poly J):ℝ:=
  let rho:ℝ:=Coat.gStep (Ψ (i+1+1)).beta/Coat.gStep (Ψ (i+1)).beta
  let wage:ℝ:=(Oak.figureReal R hk D bank π Γ books (Nat.le_succ_of_le hi) P.op P.lesson ahead order shelf).produce
    (R.family.path.levels.clock.op (i+1) per).ratio.count*P.cost
  let sites:Fin 3→Site (R.family.side (i+1) per):=(P.passport.coarser (R.family.path.levels.clock.op (i+1) per).ratio).origin
  WilsonThermometerRegisteredCapturedLedger.total (ord:=order) (σ:=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    (C:=WilsonThermometerRegisteredCapturedPace.bound rho ^(order+shelf+1)*wage) P.w
    (WilsonOlderFreshGraphPointWallet.point (0:Site (R.family.side (i+1) per))) (weights Q) (home sites)
local notation "fee" => fare R A simple top o hk D bank π Γ Ψ books hi ahead order shelf seats P

include course in
theorem original (t:Wallet disks)(Q:Poly J) {work capacity limit:ℕ}
    (hc:1 ≤ capacity)(hh:21 ≤ limit)(hw:3*order ≤ work):
    ∃ (I:Type)(M:I→Earn.Row (Earn.Passport.point (fun _:Unit=>(0:Site (R.family.side (i+1) per))))
        C₁ G (Wallet disk)), Countable I ∧ 0 ≤ fee Q ∧
      Scene.Armada M (fun _=>1) (fun _=>21) (seedWidth) (fee Q) work capacity limit ∧
      Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) disk M ∧
      ∀y:ℝ,0 < y→∀(x:Wallet disk)(U:Config G (R.family.side (i+1) per)),
        Spill.Foundry.uncut M y x U=Poly.send ((C₁).fire ())
          (amplitude disk x*((Poly.pass (WilsonRootedKioskOccupiedSlip.bare
            (rendered student (B) (oldG/current*y)) t U))*Q).part full):=by
  have walk:=course.1.walk (i+1) (Nat.le_succ_of_le hi) top.le
  have gp:0 < current:=by
    rw [walk.beta]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (Nat.lt_of_succ_lt top)))
  let r:=oldG/current
  have hr:0 < r:=div_pos P.issued.Waffle.soon.1 gp
  have seated:=P.issued.earning
  have fourteen:(∑v:Fin 3,ages v) ≤ 14:=by decide
  have places(v:Fin 3):stop (S).center ((roads) v)=(roots) v:=Earn.Cable.link_stop _ _
  have room(v:Fin 3):((roads) v).length ≤ home (roots):=by
    exact single_le_sum (f:=fun j:Fin 3=>((roads) j).length) (fun _ _=>Nat.zero_le _) (mem_univ v)
  let one:Wallet disk:=fun _=>⟨1,by simp [disk]⟩
  have all:=WilsonThermometerRegisteredCapturedMaterial.original student r hr ages P.w seated fourteen
    roads (S) t Q disk (B) P.issued.Waffle.soon (home roots) room places one
    (fun x=>(x ()).property) hc hh hw
  letI:Countable P.modelIndex:=P.modelCount
  let siz:=(R.alloy.B.a.S.oneStep (i+1) per).exact_size
  let epoch:=Oak.era R hk D bank π Γ (Nat.le_succ_of_le hi) P.op P.lesson
  let text:=Cruise.publish D R.rolls bank R.alloy φ books P.op epoch siz P.model order P.voter P.lesson.entry
  letI students:Countable (Scene.Texts P.model (Pane.panel R.alloy (i+1) siz).ratio text):=
    Scene.crewC P.model _ text (Cruise.funded D R.rolls bank R.alloy φ books P.op epoch siz P.model
      order P.voter P.lesson.entry P.lesson.studied ahead)
  let changed:=fun z=>returned r hr ((student) z)
  exact ⟨Name changed,submitted student r hr ages P.w seated fourteen roads (S) t Q disk,
    @WilsonThermometerRegisteredCapturedLedger.counted _ _ _ _ _ _ changed students,all⟩
end YM.Integration.WilsonThermometerRegisteredCapturedStudent

