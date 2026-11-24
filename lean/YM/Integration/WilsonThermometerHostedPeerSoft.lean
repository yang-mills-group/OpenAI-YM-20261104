import YM.Integration.WilsonThermometerHostedCanonical
import YM.Integration.WilsonThermometerSolitaryPeerWage

/-! Each true soft coefficient is measured with the same two ordinary peers, at their original bought width. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerHostedPeerSoft
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker
open Push Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonMeasuredCompanionFace WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {T I I':Type}[Countable I][Countable I']
local notation "CF"=>R.family
local notation "J"=>Stock.census (Fin 3)

theorem original {d N p f u:ℕ}{o:Fin 3→Site ((CF).side f p)}
    (P W:Rep G ((CF).side f p))(point:P.p=W.p)(quiet:P.eval=((CF).path.rep N p f).eval)
    (law:∃σ C Λ δ z,P.Lawful σ C Λ δ z)(fn:f≤N)(uf:u≤f)
    (a:Lamps T I G W.p o (J))(b:Lamps T I' G W.p o (J))(w:Fin 3→ℝ)(positive:∀i,0<w i)
    {α:ℝ}(ap:0≤α)(pa:a.Paid w W.p.B α 1)(pb:b.Paid w W.p.B α 1)
    (v:Fin 3)(h:Coefficient ((CF).labels.level d) ((CF).side f p))
    (fit:h.Format (o v) (CF).params P){κ B:ℝ}(bill:h.remBound (o v) P κ B)
    (x:T)(s:(J).Mode)(inside:v∈s.val):
    let Y:=fun U=>(soft h).density (o v) ((CF).localSection d) P U*
              share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s
    Integrable Y (prior G _) ∧
      companions v (Stoop.radius w 2) s*‖reading R (N:=N) (p:=p) Y u uf‖≤
        (WilsonThermometerUnitFilingFieldRange.cost G d P.p.threshold*((CF).labels.level d).coeffSize h.x+B)*
          WilsonMeasuredCompanionSoft.expense 1:=by
  intro Y
  obtain ⟨σ,C,Λ,δ,z,lawful⟩:=law
  obtain ⟨ι,cnt,Q,pay,_away,aleph⟩:=WilsonThermometerSolitaryPeerWage.original a b w positive W.p.B α ap pa pb v
  let w':=Stoop.radius w 2
  have hp i:0<w' i:=div_pos (positive i) (by norm_num)
  have reset:wage v w' (w' v)=w':=by funext i;by_cases hit:i=v <;> simp [wage,hit]
  let E:=WilsonThermometerHostedPeers.transport point Q
  have width:Q.Paid w' W.p.B α 1:=by rw [←reset];exact pay (w' v)
  have fare:E.Paid w' P.p.B α 1:=by
    rw [show P.p.B=W.p.B from congrArg BudgetPoint.B point]
    exact WilsonThermometerHostedPeers.paid point Q width
  have form:=WilsonPhysicalMarkedDefect.RegularProjection.format h (o v) P (CF).params fit
  have fee:=WilsonPhysicalMarkedDefect.RegularProjection.bill h (o v) P bill
  have peer (U):peers E v s x U=share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s:=
    (WilsonThermometerHostedPeers.peers_eq point Q v s x U).trans
      (congrArg (fun g:Poly (J)=>(g*Poly.send ((J).fire v) 1).part s) (aleph x U))
  let Z:=fun U=>(soft h).density (o v) ((CF).localSection d) P U*peers E v s x U
  have eq:Z=Y:=by funext U;dsimp only [Z,Y];rw [peer]
  have payZ:Integrable Z (prior G _):=
    WilsonMeasuredCompanionTest.integrable E v s x (soft h) form fee lawful w' hp fare ap le_rfl
  have cost:=WilsonMeasuredCompanionSoft.heard R d quiet fn v h bill E w' hp fare ap le_rfl s x u uf
  have cp:0<companions v w' s:=Finset.prod_pos fun i _=>hp i
  have total:Poly.toll w' s=companions v w' s*w' v:=(Finset.prod_erase_mul s.val w' inside).symm
  refine ⟨eq ▸ payZ,?_⟩
  rw [←eq]
  apply (mul_le_mul_of_nonneg_left cost cp.le).trans_eq
  rw [total]
  field_simp [cp.ne',(hp v).ne']

end YM.Integration.WilsonThermometerHostedPeerSoft
