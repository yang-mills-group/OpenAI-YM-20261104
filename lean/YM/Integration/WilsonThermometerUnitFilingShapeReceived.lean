import YM.Integration.WilsonThermometerUnitFilingShape
import YM.Integration.WilsonThermometerUnitFilingBirth

/-! The original stocked three-field course supplies the actual compact
unit filing and all of its genuine hard corrections at both stops. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingShapeReceived
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom
open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16 RG16.Literal

open FVA1 OriginalForcedAddresses WilsonThermometerCourseHearing WilsonThermometerCourseIntake
open WilsonPositionThermometerCapStation WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open WilsonCenteredCloseOccupiedSale WilsonCenteredCloseCaptureWallet
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ)
  (ahead : Mentor.Forecast D R.rolls bank φ books)
  (order shelf seats : ℕ) (mb : m ≤ b) (cutoff : b<N)
local notation "C" => R.family
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params

open Climb MeasureTheory Spec Table XSpace.Rose Extraction RG12 FVA1
open WilsonThermometerUnitFilingCylinder (Sites wallet source cylinder)
open WilsonThermometerUnitFilingFeed (report)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open private smooth from YM.Integration.WilsonThermometerUnitFilingDeposit
open Next.UVStress Primitives.GCC.Anchor MergeProof.East
local notation "z!" => ((N,per):UVIndex)
local notation "ms" => Sites R z!
variable (r:ℝ) (Φ:Test 3)
variable (Q : (Fin 3 → Site (R.family.side N per)) → Poly (Stock.census (Fin 3)))
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight Φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z!)
local notation "W!" => {a:ms // w! a≠0}
local notation "cut!" => WilsonThermometerUnitFilingCylinder.cylinder R A z! r Φ Q
variable (o : {a : Fin 3 → Site (R.family.side N per) //
  WilsonSeparatedOriginalThermometerCells.weight Φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r ((N,per):UVIndex)) a ≠ 0} →
  Positions (Fin 3) (R.family.side N per))
local notation "src!" y:max => offered R A simple cutoff (o y)
local notation "hist!" y:max i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R disks (src! y) i ib

/-- Pointwise qualifications supplied before the individual dated course
and its receipts have been queried. -/
def Qualified (z:UVIndex):Prop :=
    (∀ k (top:k≤z.1) (o:Positions (Fin 3) ((C).side z.1 z.2)) (s:(J).Mode),
      (fun U=>(incoming R A simple top o U).part s)=
        credit C z.1 z.2 0 (placed R A z s.val o.origin) k top) ∧
    ∀u, u≤z.1→(C).ref 0≤u→∀ r:ℝ,∀ Φ:Test 3,∀ Q:Sites R z → Poly J,
      ∀ j, u≤j→∀ top:j≤z.1,Trace.Physical.GermGraph.Opened C 0 j z.2→
        RG16.Literal.Booked C z.1 z.2 0
          (WilsonThermometerUnitFilingCylinder.cylinder R A z r Φ Q) j top

theorem before {f:Extraction.Order} {H:(Bel (C).book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (units:∀t:Fin 7,A.change t ((Bel (C).book).unit t)=(Bel (C).book).unit t) :
    ∀ᶠ z:UVIndex in f.fuse,Qualified R A simple z := by
  filter_upwards [WilsonThermometerUnitFilingReturn.density R A simple checked units,
    WilsonThermometerUnitFilingBirth.original R A simple checked units] with z value book
  refine ⟨value,?_⟩
  intro u uz cu r Φ Q j uj jz op
  obtain ⟨_,_,_,paid⟩:=book u uz cu r Φ Q
  exact (paid j uj jz op).1

include o in
private theorem integrate {i:ℕ} (top : i≤N) (qualified:Qualified R A simple z!)
    (located:∀a:W!, (o a).origin=a.val) {u v:ℕ} (cu : (C).ref 0≤u)
    (uv:u≤v) (vi:v ≤ i) (ou:Trace.Physical.GermGraph.Opened C 0 u per)
    (ov:Trace.Physical.GermGraph.Opened C 0 v per)
    (rem η:ℝ) (nonneg:0≤rem) (ηpos:0<η)
    (q0:W! → Coefficient F ((C).side i per))
    (fΘ:∀a:W!, (q0 a).Format 0 Y (Ψ i))
    (whole:∀a:W!,∀V,(q0 a).density 0 S (Ψ i) V=(total (incoming R A simple top (o a) V) (Q a)).part full ∧
      (q0 a).density 0 S (Ψ i) V=(WilsonPhysicalMarkedDefect.RegularProjection.soft (q0 a)).density 0 S ((C).path.rep N per i) V+
        WilsonMeasuredCoefficientTransport.account (q0 a) (Ψ i) V)
    (fSoft:∀a:W!,(WilsonPhysicalMarkedDefect.RegularProjection.soft (q0 a)).Format 0 Y ((C).path.rep N per i))
    (pSoft:∀a:W!,(WilsonPhysicalMarkedDefect.RegularProjection.soft (q0 a)).remBound 0 ((C).path.rep N per i)
        (Trace.Physical.GermGraph.safety C i) rem)
    (witness:∀a:W!,∀V,WilsonMeasuredCoefficientTransport.account (q0 a) (Ψ i) V≠0→
        ∃j,(q0 a).forced j V≠0 ∧ (0:Site ((C).side i per))∈(((C).path.rep N per i).activities.forced j).support ∧
          ∃x,x∈(((C).path.rep N per i).activities.forced j).inventory ∧ x∈flags ((C).path.rep N per i).p.threshold V):
    let W:=(C).path.rep N per i
    ∃ q: ms → Coefficient F ((C).side i per),
      (∀a:W!, (q a).Format 0 Y (Ψ i) ∧
        (∀V, ((q a).density 0 S (Ψ i) V)=(total (incoming R A simple top (o a) V) (Q a)).part full) ∧
        ∀V,WilsonMeasuredCoefficientTransport.account (q a) (Ψ i) V≠0→
          ∃j,(q a).forced j V≠0 ∧ (0:Site ((C).side i per))∈(W.activities.forced j).support ∧
            ∃x,x∈(W.activities.forced j).inventory ∧ x∈flags W.p.threshold V) ∧
      ‖(report R (cut!) u-report R (cut!) v)-
        ∑y,w! y*(reading R (N:=N) (WilsonMeasuredCoefficientTransport.account (q y) (Ψ i)) u (uv.trans vi)-
          reading R (N:=N) (WilsonMeasuredCoefficientTransport.account (q y) (Ψ i)) v vi)‖ ≤
        (∫x:Points 3,‖Φ x‖)*(2*capital C i rem η*Real.exp (-((C).S.scale i-(C).S.scale v)/8)) := by
  intro W
  let q (a:ms) : Coefficient F ((C).side i per):=
    if ha:w! a≠0 then q0 ⟨a,ha⟩ else Extra.Histories.primary 0 0
  have atq (a:W!):q a=q0 a:=dif_pos a.property
  apply Exists.intro q
  constructor
  · intro a
    rw [atq];exact ⟨fΘ a,fun V=>(whole a V).1,witness a⟩
  · obtain ⟨heads,books⟩:=qualified
    have uvN:=uv.trans (vi.trans top)
    apply WilsonThermometerUnitFilingShape.original R simple A z! r Φ Q cu uv vi top ou ov
      (books u uvN cu r Φ Q u le_rfl uvN ou) (books u uvN cu r Φ Q v uv (vi.trans top) ov)
      (fun _=>Ψ i) q rem η nonneg ηpos
    intro a ha
    let a' : W!:=⟨a,ha⟩
    rw [show q a=q0 a' from dif_pos ha]
    refine ⟨fSoft a',?_,?_⟩
    · exact rem_mono (pSoft a') le_rfl
    · funext V
      have line:credit C N per 0 (WilsonThermometerUnitFilingCylinder.source R A z! a (Q a)) i top V=
        (total (incoming R A simple top (o a') V) (Q a)).part full := by
        rw [WilsonThermometerUnitFilingCylinder.source,IntrinsicProductLinearity.credit_sum C N per 0 i top _ _
          (smooth R A z! a),Finset.sum_apply,affine]
        simp only [Pi.smul_apply,smul_eq_mul]
        apply sum_congr rfl;intro s _
        apply congrArg (_ * ·)
        simpa only [located] using (congrFun (heads i top (o a') s) V).symm
      exact line.trans ((whole a' V).1.symm.trans (whole a' V).2)

include o in
theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (qualified:Qualified R A simple z!) (located:∀a:W!, (o a).origin=a.val)
    (initial : ∀a:W!,post b mb (src! a)) (h : ℕ) (U α : ℝ) (income : 0 ≤ U)
    (paid : ∀a:W!,WilsonReceivedCloseNamedWallet.Sold R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats
      mb (src! a) (initial a) univ (U*((g b)⁻¹)^h))
    (degree : ℕ) (cap : ℝ) (close : PaceR.Close R degree cap m b)
    (travel : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (gallery : (eventually_atTop.mp (WilsonReceivedCloseGalleryWallet.reserve R simple (max 1 3)
      (show (0:ℝ)<1 by norm_num))).choose ≤ m)
    (slow : ∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (rays : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ m)
    (before : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ m)
    (eligible : WilsonCenteredCaptureClock.first R simple ≤ m)
    (way : WayStation R.kit) (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    {i : ℕ} (ib : i ≤ b) (mi : m ≤ i) (L : ∀a:W!,post i mi (hist! a i ib))
    (trail:∀a:W!,WilsonReceivedCloseHistory.Trail R hk D bank π Γ Ψ books ahead disks sectors ages order shelf seats
      mb (src! a) (initial a) i mi (hist! a i ib) (L a))
    (stages : shelf≤R.alloy.B.a.clock.J i) (size:∀a:W!, (L a).op.count≤Burn.horizon k+2)
    (supp : ((C).path.levels.budget i).supportExponent≤α)
    (sec:R.t 0 ≤ i) (refs:∀j:Fin 3,(C).ref (WilsonPositionThermometerGradedSource.grade j)≤N)
    (Z:W!→Support ((C).side i per)) (rad:W!→ℕ)
    (center:∀a:W!,(0:Site ((C).side i per))∈Z a)
    (home:∀a:W!,∀j:Fin 3,((L a).passport.coarser (move i).ratio).origin j∈Z a)
    (near:∀a:W!,∀j:Fin 3,separation (((L a).passport.coarser (move i).ratio).origin j) 0≤rad a)
    (short:∀a:W!,rad a≤((C).path.levels.budget i).B)
    (inside:∀a:W!,Z a⊆halo ((C).path.levels.budget i).B {0})
    (t:ℝ) (invoice:ℕ) (banked:∀a:W!,(g (i+1))^invoice*(∑s:(J).Mode,‖WilsonThermometerCenteredAlgebra.weight (Q a.val) s‖)≤t)
    {u v:ℕ} (cu:(C).ref 0≤u) (uv:u≤v) (vi:v ≤ i)
    (ou:Trace.Physical.GermGraph.Opened C 0 u per) (ov:Trace.Physical.GermGraph.Opened C 0 v per)
    (η:ℝ) (ηpos:0<η) :
    let W:=(C).path.rep N per i
    let e:=exponent seats h 3
    let price:=WilsonCenteredCloseOccupiedSale.amount G 0 seats h 3 α U
    let rem:=max 0 (t*price/(g (i+1))^(invoice+e))
    ∃ q: ms → Coefficient F ((C).side i per),
      (∀a:W!, (q a).Format 0 Y (Ψ i) ∧
        (∀V, ((q a).density 0 S (Ψ i) V)=(total (incoming R A simple (ib.trans_lt cutoff).le (o a) V) (Q a)).part full) ∧
        ∀V,WilsonMeasuredCoefficientTransport.account (q a) (Ψ i) V≠0→
          ∃j,(q a).forced j V≠0 ∧ (0:Site ((C).side i per))∈(W.activities.forced j).support ∧
            ∃x,x∈(W.activities.forced j).inventory ∧ x∈flags W.p.threshold V) ∧
      ‖(report R (cut!) u-report R (cut!) v)-
        ∑y,w! y*(reading R (N:=N) (WilsonMeasuredCoefficientTransport.account (q y) (Ψ i)) u (uv.trans vi)-
          reading R (N:=N) (WilsonMeasuredCoefficientTransport.account (q y) (Ψ i)) v vi)‖ ≤
        (∫x:Points 3,‖Φ x‖)*(2*capital C i rem η*Real.exp (-((C).S.scale i-(C).S.scale v)/8)) := by
  intro W e price rem
  let top: i≤N:=(ib.trans_lt cutoff).le
  choose q0 _fR _pR fΘ _pΘ whole fSoft pSoft witness using fun a : W! => 
    WilsonThermometerCanonicalHearing.original R A simple hk D bank π Γ Ψ books ahead order shelf seats
      mb cutoff (o a) course (initial a) h U α income (paid a) degree cap close travel gallery slow ready rays
      before eligible way pass hospital ib mi (L a) (trail a) stages (size a) supp sec refs (Z a) 0
      (rad a) (center a) (home a) (near a) (short a) (inside a) (Q a) t invoice (banked a)
  apply integrate R A simple Ψ r Φ Q o top qualified located cu uv vi ou ov rem η (le_max_left ..) ηpos
    q0 fΘ (fun a V=>⟨(whole a V).1,(whole a V).2.2⟩) fSoft _ witness
  intro a
  exact rem_mono (pSoft a) (le_max_right ..)

end YM.Integration.WilsonThermometerUnitFilingShapeReceived
