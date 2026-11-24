import YM.Integration.WilsonRegisteredPairUnaryWallet
import YM.Integration.WilsonGeometricSignedCapture

/-! The actual registered ordinary table at capture as a univariate marked source on its original Wilson vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedQNominalWallet
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture WilsonRegisteredPairUnaryWallet

open WilsonThermometerRegisteredCapturedPace WilsonThermometerRegisteredCapturedUncut
open WilsonThermometerRegisteredCapturedSector WilsonThermometerRegisteredCapturedLedger
local notation "J"=>Stock.census (Fin 3)
local notation "C₁"=>Stock.census Unit
/-- A coefficient is filed at the complementary marker so that the full slot reads the
specified signed combination of the actual ordinary faces. -/
def selection (c:(J).Mode → ℂ) : Poly J := fun s => c (complement s)

theorem selected (c:(J).Mode → ℂ) (s:(J).Mode):
    weights (selection c) s=c s:= by
  have involution:∀a:(J).Mode,complement (complement a)=a:=by decide
  change c (complement (complement s))=c s
  rw [involution]

theorem read_selection (c:(J).Mode → ℂ) (F:Poly J):
    (F*selection c).part full=WilsonGeometricSignedCapture.take c F:=by
  have complete:∀a b:(J).Mode, Poly.merges a b full ↔ b=complement a:=by decide
  rw [Poly.part_mul]
  simp only [complete,Finset.sum_ite_eq',mem_univ,if_true]
  apply sum_congr rfl
  intro a _
  change F.part a*weights (selection c) a=c a*F.part a
  rw [selected,mul_comm]

variable {G:Gauge} (R:Run G) {m j N per k:ℕ}
  (top:j < N) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls bank φ) (inside:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls bank φ books) (order shelf seats:ℕ)
  {X:Fin 3→Type} [∀v,AddCommGroup (X v)] [∀v,Module ℝ (X v)]
  (actors:∀v,Set (X v)) (pieces:∀v,Submodule ℝ (X v)) (ages:Fin 3→ℕ)
  (physical:Wallet actors → Config G (R.family.side (j+1) per)→Poly J)
  (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces ages order shelf seats j inside physical)
  (origin:Site (R.family.side j per))
local notation "sheet"=>R.family.path.levels.clock.op j per
local notation "student"=>Oak.student (n:=per) R hk D bank π Γ books inside P.op P.lesson ahead actors P.model order P.voter
local notation "fig"=>Oak.figureReal R hk D bank π Γ books inside P.op P.lesson ahead order shelf
local notation "oldG"=>Coat.gStep (Ψ (j+1)).beta
local notation "current"=>Coat.gStep (Ψ j).beta
local notation "seedWidth"=>Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J j)
local notation "price"=> (fig).produce (sheet).ratio.count*P.cost
local notation "S"=>WilsonOlderFreshGraphPointWallet.point origin
local notation "roots"=>(P.passport.coarser (sheet).ratio).origin
local notation "roads"=>(fun v:Fin 3=>Earn.Cable.link origin ((roots) v))
local notation "B"=> (Ψ j).p

include course top in
theorem original (c:(J).Mode→ℂ) (t:Wallet actors) (totalAge:(∑v,ages v)≤14)
    {work capacity limit:ℕ} (hc:1≤capacity)(hh:21≤limit)(hw:3*order≤work):
    let Q:=selection c
    let fee:=WilsonThermometerRegisteredCapturedLedger.total (ord:=order) (σ:=(seedWidth))
      (C:=(bound (oldG/current))^(order+shelf+1)*(price)) P.w (S) (weights Q) (reach origin roots)
    ∃ (I:Type)(M:I→Earn.Row (Earn.Passport.point (fun _:Unit=>origin)) C₁ G (Wallet disk)),
      Countable I ∧ 0≤fee ∧ Scene.Armada M (fun _=>1) (fun _=>21) (seedWidth) fee work capacity limit ∧
      Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) disk M ∧
      ∀y:ℝ,0<y→∀(x:Wallet disk)(U:Config G (R.family.side j per)),
        let F:=Poly.pass (WilsonRootedKioskOccupiedSlip.bare
          (rendered student (B) (oldG/current*y)) t U)
        Spill.Foundry.uncut M y x U=Poly.send ((C₁).fire ())
          (amplitude disk x*(WilsonGeometricSignedCapture.take c F)):=by
  intro Q fee
  have walk:=course.1.walk j inside top.le
  have gp:0 < current:=by
    rw [walk.beta]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson top.le))
  let ratio:=oldG/current
  have hr:0 < ratio:=div_pos P.issued.Waffle.soon.1 gp
  have incidence(v:Fin 3):stop (S).center ((roads) v)=(roots) v:=Earn.Cable.link_stop _ _
  have lengths(v:Fin 3):((roads) v).length ≤ reach origin (roots):=
    single_le_sum (f:=fun z:Fin 3=>((roads) z).length) (fun _ _=>Nat.zero_le _) (mem_univ v)
  let one:Wallet disk:=fun _=>⟨1,by simp [disk]⟩
  have sold:=WilsonThermometerRegisteredCapturedMaterial.original student ratio hr ages P.w P.issued.earning
    totalAge roads (S) t Q disk (B) P.issued.Waffle.soon (reach origin roots) lengths incidence one
    (fun x=>(x ()).property) hc hh hw
  letI:Countable P.modelIndex:=P.modelCount
  let siz:=(R.alloy.B.a.S.oneStep j per).exact_size
  let epoch:=Oak.era R hk D bank π Γ inside P.op P.lesson
  let text:=Cruise.publish D R.rolls bank R.alloy φ books P.op epoch siz P.model order P.voter P.lesson.entry
  letI students:Countable (Scene.Texts P.model (Pane.panel R.alloy j siz).ratio text):=
    Scene.crewC P.model _ text (Cruise.funded D R.rolls bank R.alloy φ books P.op epoch siz P.model
      order P.voter P.lesson.entry P.lesson.studied ahead)
  let changed:=fun z=>returned ratio hr ((student) z)
  refine ⟨Name changed,submitted student ratio hr ages P.w P.issued.earning totalAge roads (S) t Q disk,
    @WilsonThermometerRegisteredCapturedLedger.counted _ _ _ _ _ _ changed students,sold.1,sold.2.1,sold.2.2.1,?_⟩
  intro y hy x U
  have exactRead:=sold.2.2.2 y hy x U
  rw [show Q=selection c from rfl,read_selection] at exactRead
  exact exactRead
end YM.Integration.WilsonReceivedQNominalWallet
