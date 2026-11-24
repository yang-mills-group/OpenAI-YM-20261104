import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFreshPostedRow
import YM.Comparison.RG02.Cumulants.Parents
import YM.FormalOPE.RG10.MarkerLog

/-! On one normalized, possibly already multiply marked history, compare two
fresh postings before and after taking the original positive expectation.
The unaltered older mixed activity cancels exactly; after averaging the
remaining mixed difference is a covariance with the complete older singleton
on the same path. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Set MeasureTheory Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V]{C:Census V}

def postedUnit (old:Poly C)(u:V→ℂ):Poly C:=Poly.pass (∑i:V,Poly.send (C.fire i) (u i))*old

private theorem unit_rows (old:Poly C)(hu:old.part C.quiet=1)(u:V→ℂ)(a:V):
    (postedUnit old u).part C.quiet=1 ∧ (postedUnit old u).part (C.fire a)=old.part (C.fire a)+u a:=by
  constructor
  · unfold postedUnit
    rw [Poly.quiet_mul,pass_fire,hu,mul_one]
    rfl
  change (_*old).part (C.fire a)=_
  rw [first_mul,pass_fire,pass_fire,hu]
  simp [Census.quiet,Census.fire]

private theorem connected_post (old:Poly C)(unit:old.part C.quiet=1)(u:V→ℂ):
    connected (postedUnit old u)=(∑i:V,Poly.send (C.fire i) (u i))+connected old:=by
  let e:Poly C:=∑ i:V,Poly.send (C.fire i) (u i)
  have quiet:e.part C.quiet=0:=by simp [e,Poly.part_sum,Poly.part_send,Ne.symm (C.fire_hot _)]
  change connected (e.pass*old)=e+connected old
  rw [FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part _ quiet) unit,FormalOPE.RG10.PolyUtil.conn_pass _ quiet]

/-- No hypothesis on the old pair or on either old singleton. The two fresh
choices agree at b and may change at other labels. The entire connected
old pair therefore cancels at the same field before any integration. -/
theorem posted_pair_increment (old:Poly C)(unit:old.part C.quiet=1)(u v:V→ℂ)(a b:V)(separate:a≠b)
    (s:C.Mode)(pair:s.val={a,b})(unchanged:u b=v b):
    (postedUnit old u).part s-(postedUnit old v).part s=(u a-v a)*(old.part (C.fire b)+v b):=by
  have zero(z:V→ℂ): (∑i:V,Poly.send (C.fire i) (z i)).part s=0:=by
    rw [Poly.part_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Poly.part_send,if_neg]
    intro e
    have h:=congrArg (fun p:C.Mode=>p.val.card) e
    simp [Census.fire,pair,separate] at h
  have conn: (connected (postedUnit old u)).part s=(connected (postedUnit old v)).part s:=by
    simp only [connected_post old unit,Poly.part_plus,zero,zero_add]
  have ua:=unit_rows old unit u a
  have va:=unit_rows old unit v a
  rw [twins a b s _ ua.1 separate pair,twins a b s _ va.1 separate pair,ua.2,va.2,
    (unit_rows old unit u b).2,(unit_rows old unit v b).2,unchanged] at conn
  linear_combination conn

/-- Complete, connected two-source reading of the averaged polynomial. No
replacement of the physical law by the product of its singleton marginals. -/
def jointPostMean {X:Type*}[MeasurableSpace X](μ:Measure X)(old:X→Poly C)(u:X→V→ℂ):Poly C:=
  fun s=>∫x,(postedUnit (old x) (u x)).part s ∂μ

theorem original_posted_covariance {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    (old:X→Poly C)(unit:∀x,(old x).part C.quiet=1)(u v:X→V→ℂ)(a b:V)(apart:a≠b)
    (s:C.Mode)(pair:s.val={a,b})(ub:∀x,u x b=v x b)
    (mu:∀t:C.Mode,Integrable (fun x=>(postedUnit (old x) (u x)).part t) μ)
    (mv:∀t:C.Mode,Integrable (fun x=>(postedUnit (old x) (v x)).part t) μ):
    let δ:=fun x=>u x a-v x a
    let h:=fun x=>(old x).part (C.fire b)+v x b
    let out:=connected (jointPostMean μ old u)
    let baseline:=connected (jointPostMean μ old v)
    out.part s-baseline.part s=(∫x,δ x*h x ∂μ)-(∫x,δ x ∂μ)*(∫x,h x ∂μ):=by
  intro δ h out baseline
  have cash (z:X→V→ℂ):(jointPostMean μ old z).part C.quiet=1:=by
    change (∫x,(postedUnit (old x) (z x)).part C.quiet ∂μ)=1
    simp only [(unit_rows _ (unit _) _ a).1,integral_const,probReal_univ,one_smul]
  have signed(t:C.Mode):(jointPostMean μ old u).part t-(jointPostMean μ old v).part t=
      ∫x,(postedUnit (old x) (u x)).part t-(postedUnit (old x) (v x)).part t ∂μ:=
    (integral_sub (mu t) (mv t)).symm
  have al:(jointPostMean μ old u).part (C.fire a)-(jointPostMean μ old v).part (C.fire a)=∫x,δ x ∂μ:=by
    rw [signed];apply integral_congr_ae
    filter_upwards with x
    dsimp only [δ]
    rw [(unit_rows _ (unit x) _ a).2,(unit_rows _ (unit x) _ a).2];abel
  have bl(z:X→V→ℂ)(hb:∀x,z x b=v x b):(jointPostMean μ old z).part (C.fire b)=∫x,h x ∂μ:=by
    apply integral_congr_ae
    filter_upwards with x
    exact ((unit_rows _ (unit x) _ b).2).trans (congrArg (_+·) (hb x))
  have both:(jointPostMean μ old u).part s-(jointPostMean μ old v).part s=∫x,δ x*h x ∂μ:=by
    rw [signed];apply integral_congr_ae
    filter_upwards with x
    exact posted_pair_increment _ (unit x) _ _ a b apart s pair (ub x)
  change (connected _).part s-(connected _).part s=_
  rw [twins a b s _ (cash u) apart pair,twins a b s _ (cash v) apart pair,bl u ub,bl v (fun _=>rfl),←al,←both]
  ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
