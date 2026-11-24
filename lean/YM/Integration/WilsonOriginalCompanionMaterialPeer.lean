import YM.Integration.WilsonOriginalCompanionBeforePeer
import YM.Integration.WilsonOriginalCompanionCoursePeers
import YM.Integration.WilsonOriginalCompanionCellRoots

/-! A signed canonical hard account with both original ordinary peers at every shifted physical cell. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionMaterialPeer
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

private theorem margin {x a b:ℝ}(paid:∀e:ℝ,0<e → x≤a*(b+e)):x≤a*b:=by
  by_contra! bad
  let e:=(x-a*b)/(2*(|a|+1))
  have positive:0<2*(|a|+1):=by positivity
  have ep:0<e:=div_pos (sub_pos.mpr bad) positive
  have balance:e*(2*(|a|+1))=x-a*b:=div_mul_cancel₀ _ positive.ne'
  have gap:=mul_le_mul_of_nonneg_right (le_abs_self a) ep.le
  nlinarith [paid e ep,mul_nonneg (abs_nonneg a) ep.le]

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
    a.Paid w (Ψ f).p.B (Ψ f).p.supportExponent 1 → b.Paid w (Ψ f).p.B (Ψ f).p.supportExponent 1 →
    ∀(v:Fin 3){d:ℕ}{F:Frame G d}(h:Coefficient F ((CF).side f p))(hol:Hol G)(S:SectionData F)(B:ℝ),0≤B →
      h.Format (o v) hol P → h.remBound (o v) P (LocalComparison.forcedDivisor (CF) f) B →
    ∀(t:T→ℂ),(∀x,‖t x‖≤1) →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let Y:=fun U=>t x*(h.density (o v) S P U-(soft h).density (o v) S P U)*
      share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s
    Integrable Y (prior G _) ∧ companions v (Stoop.radius w 2) s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
        WilsonOriginalCompanionPeerRefund.tariff*B*(regulatorRun (CF) N p f)^q:=by
  filter_upwards [WilsonOriginalCompanionBeforePeer.original R simple cater bank book c 81 q,
    WilsonOriginalCompanionCellRoots.original R simple φ] with j treasury homes
  intro N p f height fn days expo r span y active o P m k π Γ Ψ course birth T I I' inst inst' a b w
    pos pa pb v d F h hol S B bp legal bound t unit u ref uj ou oj x s inside Y
  obtain ⟨start,parents,cover,held⟩:=homes N p f height fn r span y active
  obtain ⟨ι,count,E,raised,same⟩:=WilsonOriginalCompanionCoursePeers.original R π Γ Ψ course birth fn o a b w pos pa pb v
  have weight:∀i,0<Stoop.radius w 2 i:=fun i=>div_pos (pos i) (by norm_num)
  have field(U):peers E v s x U=
      share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s:=
    congrArg (fun P:Poly (J)=>(P*Poly.send ((J).fire v) 1).part s) (same x U)
  have invoice(e:ℝ)(ep:0<e):Integrable Y (prior G _) ∧ companions v (Stoop.radius w 2) s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
        WilsonOriginalCompanionPeerRefund.tariff*(B+e)*(regulatorRun (CF) N p f)^q:=by
    have exactPaid:=treasury T ι hol S N p f height fn days o v h t E (Stoop.radius w 2) B e
      (WilsonOriginalCompanionCellRoots.route R y) WilsonOriginalCompanionCellRoots.center
      weight bp ep start parents expo legal bound unit raised cover held u ref uj ou oj x s inside
    simpa only [field,Y] using exactPaid
  refine ⟨(invoice 1 (by norm_num)).1,?_⟩
  have paid(e:ℝ)(ep:0<e):companions v (Stoop.radius w 2) s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
       (WilsonOriginalCompanionPeerRefund.tariff*(regulatorRun (CF) N p f)^q)*(B+e):=by
    simpa only [mul_right_comm] using (invoice e ep).2
  simpa only [mul_right_comm] using margin paid

end YM.Integration.WilsonOriginalCompanionMaterialPeer
end
