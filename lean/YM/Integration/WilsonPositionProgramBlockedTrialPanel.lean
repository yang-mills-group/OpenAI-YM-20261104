import YM.Integration.WilsonPositionProgramBlockedTrialSalary
import YM.Integration.WilsonCapturedPrimaryEstimate
import YM.Integration.WilsonMasterCoordinatePrice
/-! Complete measured coordinates of the solved interior trial. Two uses of
the actual returned marked wage are distinguished: the projected tail of the
full regular series, and the value discarded at each clipped real node. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialPanel
open Function Filter Finset Labels Lattice Wilson RG Source Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCapturedPrimaryCollar WilsonCapturedPrimaryReading WilsonCapturedPrimaryEstimate
open WilsonFirstReceivedRadialStencil WilsonMasterReportingWords Next.Rank RG16 RG16.Literal
open scoped Classical BigOperators Topology

def fee {G:Gauge} {d:ℕ} (F:Frame G d) (A:Hol G) : ℝ :=
  testPrice F * ∑ p∈tests F,probeFee A p

theorem cropped {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{n:Side}{o:Site n}{W:Rep G n}
    (q:Coefficient F n) (form:q.Format o A W) {κ rough:ℝ} (paid:q.remBound o W κ rough)
    (order:d≤W.p.order) (power:d≤W.p.power) (r:ℕ) :
    F.coeffSize (projection F A W.p.threshold o q-
      projection F A W.p.threshold o (kept q W.p r)) ≤
      fee F A*(Real.exp (-(W.p.supportExponent*r))*rough):=by
  let a:=Real.exp (-(W.p.supportExponent*r))*rough
  have rq:0≤rough:=by obtain ⟨u,v,hu,hv,ht,_⟩:=paid;linarith
  have pos:0≤a:=mul_nonneg (Real.exp_pos _).le rq
  have h:=returned (R:=W) (A:=A) (o:=o) q (projection F A W.p.threshold o (kept q W.p r))
    (fun p=>probeFee A p*a) (fun p _=>mul_nonneg (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose_spec.1 pos)
    (fun p _=>by simpa only [probeFee,mul_assoc] using coordinate form paid order power r p)
  rwa [←Finset.sum_mul,←mul_assoc] at h

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path
local notation "P₀" => (C₀).params

def Heard (N p b:ℕ)(e:(C₀).label d)(q:Coefficient F₀ ((C₀).side b p)) : Prop :=
  let W:=(H₀).rep N p b
  let H:=2*stock C₀ b*(F₀).coeffSize e
  ∀ r:ℕ,
    (F₀).coeffSize (gMap C₀ N p d b (e-projection F₀ P₀ W.p.threshold 0 (kept q W.p r))) ≤
      (2:ℝ)^(degree F₀)*fee F₀ P₀*(Real.exp (-(W.p.supportExponent*r))*H) ∧
    ∀ U:Config G ((C₀).side b p),
      let V:=clip 0 (radius W.p r) U
      flags W.p.threshold V=∅ →
      ‖reading B₀ W 0 q V - reading B₀ W 0 (kept q W.p r) V‖≤Real.exp (-(W.p.supportExponent*r))*H

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (ep:0<η):
    ∀ᶠ b:ℕ in atTop,∀ N p n,∀ live:b+n≤N, let W:=(H₀).rep N p b
      let out:=WilsonPositionProgramOriginalBlockedTrial.carried R d (p:=p) live 0
      ∃ A:(C₀).label d ≃ₗ[ℂ] (C₀).label d,∀ e:(C₀).label d,let w:=A.symm e
        (F₀).coeffSize w ≤ 2*Real.exp (η*((C₀).S.scale (b+n)-(C₀).S.scale b))*(F₀).coeffSize e ∧
        ∃ q:Coefficient F₀ ((C₀).side b p),q.Format 0 P₀ W ∧
          q.remBound 0 W (safety C₀ b) (2*stock C₀ b*(F₀).coeffSize e) ∧
          q.density 0 B₀ W=out w ∧ projection F₀ P₀ W.p.threshold 0 q=e ∧ Heard R d N p b e q:=by
  filter_upwards [WilsonPositionProgramBlockedTrialSalary.original R shop d simple ep,
    eventually_ge_atTop ((C₀).ref d)] with b full ref
  intro N p n live W out
  have current:b≤N:=by omega
  obtain ⟨rk,ord⟩:=dimensions d N p b R.makes ref current
  obtain ⟨A,hA⟩:=full N p n live
  refine ⟨A,?_⟩;intro e w
  obtain ⟨price,q,hq,rem,_,field,measured⟩:=hA e
  refine ⟨price,q,hq,rem,field,measured,?_⟩
  intro r; refine ⟨?_,fun U clear=>omitted (R.makes.sections d) rem r _ clear⟩
  have gross:=WilsonMasterCoordinatePrice.positive_grade R.makes N p d b current
    (e-projection F₀ P₀ W.p.threshold 0 (kept q W.p r))
  have h:=cropped q hq rem rk ord r
  rw [measured] at h
  exact gross.trans ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (mul_assoc ..).symm)

end YM.Integration.WilsonPositionProgramBlockedTrialPanel
end
