import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! The entire original joint test evaluates the single tensor deposited by its measured source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedFunctional
open Laurent Bloch Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open XSpace XSpace.Rose RegulatorIR RegulatorIR.Cluster PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonOriginalPublicNodalTestedRoster (cash)
open WilsonOriginalPublicNodalTestedChronology (registered tender rank)
open WilsonIndependentRawPhysicalFaces (ordered)
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)

def deposit (S:Finset I):Pen D S:=
  (ContinuousMap.evalCLM ℝ (fun i=>(κ i,pt i))).comp (area D S).subtypeL

omit [Fintype I] [DecidableEq I] in
theorem visits (S:Finset I)(A:Case D):
    touch A S (deposit D κ pt S)=∏i:S,claim (D i) (κ i) (pt i) (A i):=by
  change (∏i∈S,claim (D i) (κ i) (pt i) (A i))=_
  rw [←Finset.prod_coe_sort S]

def power (S:Finset I):Cost:=∏i:S,(PowerSeries.X:Cost)^(((R.family.labels.level (d i)).grades (b i)).2)
def charge (S:Finset I)(test:Pen D S→L[ℝ] ℝ):Cost:=PowerSeries.C (test (deposit D κ pt S))*power R d b S

omit [Fintype I] [DecidableEq I] in
theorem paid (S:Finset I)(A:Case D):
    tender R D d b κ pt A S=charge R D d b κ pt S (touch A S):=by
  unfold tender cash charge power
  rw [visits,Finset.prod_mul_distrib,map_prod]

private theorem scaled {U:Type}(a:ℝ)(p:Cost)(X:Pal ℝ U)(e r:ℕ)(x:Fin r→U):
    affix (PowerSeries.C a*p) X e r x=a*affix p X e r x:=by
  simp [affix,Finset.sum_apply,Finset.mul_sum,PowerSeries.coeff_C_mul,mul_assoc]

variable {stamps:I→ℕ}(cut:∀i,d i<stamps i)(o:I → Cover)

theorem original (S:Finset I)[Nonempty S](test:Pen D S→L[ℝ] ℝ):
    tuftV test (levelsO (WilsonOlderFreshSoftFigures.stencil R D d b κ pt o) S)=
    affiled (charge R D d b κ pt S test) (registered R W d b cut o S):=by
  let M:=WilsonOlderFreshSoftFigures.stencil R D d b κ pt o
  let raw:=registered R W d b cut o S
  let ink:=power R d b S
  let stamp:=deposit D κ pt S
  have genuine:Auth (rank R d b S) raw:=WilsonIndependentMatchedOpeningRoster.enrolled R W
    (fun _:S=>false) (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have yes:=((placedO M ((sold b κ pt).1.level' o) S).tuft test)
  have entered (n:Side)(e r:ℕ)(x:Fin r→Woods G n):
      (levelsO M S).1 n e r x=(affix ink (raw.1 n) e r x) • stamp:=by
    apply pen_inj
    intro A
    have h:=congrArg (fun P:Era G ℝ=>P.1 n e r x) (WilsonOriginalPublicNodalTestedRoster.original R W D d b κ pt cut o A S)
    change touch A S ((levelsO M S).1 n e r x)=affix (tender R D d b κ pt A S) (raw.1 n) e r x at h
    rw [h,paid,charge,scaled,map_smul]
    exact mul_comm _ _
  apply yes.ext (WilsonIndependentMatchedOpeningFee.grant _ genuine _)
  funext n e r x
  change test ((levelsO M S).1 n e r x)=affix (charge R D d b κ pt S test) (raw.1 n) e r x
  rw [entered,charge,scaled,map_smul]
  exact mul_comm _ _

end YM.Integration.WilsonOriginalPublicNodalTestedFunctional
end
