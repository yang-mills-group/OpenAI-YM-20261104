import YM.Integration.WilsonOriginalCompanionLowerPeer
import YM.Integration.WilsonOriginalCompanionCoursePeers
import YM.Integration.WilsonOriginalCompanionCellRoots

/-! The same two genuinely fired ordinary peer rosters at the lower physical support exponent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionLowerMaterial
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCompanionFace
open WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open WilsonOriginalCompanionCellRoots WilsonThermometerOwnOffsetJoint
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "J"=>Stock.census (Fin 3)
open Extraction Cells XSpace WilsonThermometerAlignedCells


private theorem transport {n:Side}{T I:Type}{o:Fin 3→Site n}{P W:BudgetPoint}(pts:P=W)(α:ℝ)
    (E:Lamps T I G P o (J))(v:Fin 3)(w:Fin 3→ℝ)
    (pay:∀h:ℝ,E.Paid (wage v w h) P.B α 1):
    ∃L:Lamps T I G W o (J),(∀h:ℝ,L.Paid (wage v w h) W.B α 1) ∧ ∀x U,L.log x U=E.log x U:=by
  subst W
  exact ⟨E,pay,fun _ _=>rfl⟩

theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(book:WilsonReportLampForecast.Ready (A))
    (φ:Test 3)(c q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (_:f≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 → 0≤((A).budget f).supportExponent-2 →
    ∀r:ℝ,|r|≤(CF).S.a (j+1) →
    ∀y:Site ((CF).side N p)×Site ((CF).side N p),mass (R:=R) r (N,p) φ y≠0 →
    let o:=origins R (atOrigin y) f
    let P:=(CF).path.rep N p f
    ∀(m k:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((CF).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ → m≤f →
    ∀(T I I':Type)[Countable I][Countable I'](a:Lamps T I G (Ψ f).p o (J))
      (b:Lamps T I' G (Ψ f).p o (J))(w:Fin 3→ℝ),(∀v,0<w v) →
    a.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 → b.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 →
    ∀(v:Fin 3){d:ℕ}{F:Frame G d}(h:Coefficient F ((CF).side f p))(hol:Hol G)(S:SectionData F)(B:ℝ),0≤B →
      h.Format (o v) hol P → h.remBound (o v) P (LocalComparison.forcedDivisor (CF) f) B →
    ∀(t:T→ℂ),(∀x,‖t x‖≤1) →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let Y:=fun U=>t x*(h.density (o v) S P U-(soft h).density (o v) S P U)*
      share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s
    Integrable Y (prior G _) ∧ companions v (Stoop.radius w 2) s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
        WilsonOriginalCompanionLowerPeer.tariff*B*(regulatorRun (CF) N p f)^q:=by
  filter_upwards [WilsonOriginalCompanionLowerPeer.original R simple cater bank book φ c q] with j purchased
  intro N p f height fn days expo r span y active o P m k π Γ Ψ course birth T I I' inst inst' a b w
    pos pa pb v d F h hol S B bp fit bound t unit u ref uj ou oj x s inside Y
  obtain ⟨ι,count,E,paid,_free,same⟩:=WilsonThermometerSolitaryPeerWage.original a b w pos _ _ expo pa pb v
  have eq:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course birth fn).1
  obtain ⟨L,pay,field⟩:=transport eq.symm _ E v (Stoop.radius w 2) paid
  have id(U):peers L v s x U=share (fun i=>(a.log x U).part ((J).fire i))
      (fun i=>(b.log x U).part ((J).fire i)) v s:=
    congrArg (fun z:Poly (J)=>(z*Poly.send ((J).fire v) 1).part s) ((congrArg Poly.pass (field x U)).trans (same x U))
  have check:=purchased N p f height fn days expo r span y active T ι L (Stoop.radius w 2) v
    (fun i=>div_pos (pos i) (by norm_num)) pay h hol S B bp fit bound t unit u ref uj ou oj x s inside
  simpa only [id,Y] using check

end YM.Integration.WilsonOriginalCompanionLowerMaterial
end
