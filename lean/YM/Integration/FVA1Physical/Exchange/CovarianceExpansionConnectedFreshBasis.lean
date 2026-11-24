import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFreshReplicatedBasis
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionConnectedReplica

/-! The connected two-direction secant after averaging, on any normalized
finite-regulator law carrying the actual old table. All singleton and old-pair
deposits remain in each of its four separate settings before subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Marker Multi Comparison.RG02.Cumulants MeasureTheory RG
open scoped Classical
open private unit_rows from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPostedCovariance
variable {V:Type} [Fintype V] [DecidableEq V] {C:Census V} {X:Type*} [MeasurableSpace X]

def twoBirthSettings (a b:V)(A B:Bool)(f h:X→ℂ)(x:X):V→ℂ :=
  (if A then Pi.single a (f x) else 0)+(if B then Pi.single b (h x) else 0)

theorem integrated_fresh_connected (μ:Measure X)[IsProbabilityMeasure μ]
    (old:X→Poly C)(unit:∀x,(old x).part C.quiet=1)(a b:V)(apart:a≠b)
    (s:C.Mode)(pair:s.val={a,b})(f h:X→ℂ)(he:Envelope h)(fe:Envelope f)
    (admitted:∀(A B:Bool)(r:C.Mode),
      Integrable (fun x=>(postedUnit (old x) (twoBirthSettings a b A B f h x)).part r) μ):
    let Q:=fun A B=>(Extra.Trajectories.connected (jointPostMean μ old (twoBirthSettings a b A B f h))).part s
    (Q true true-Q false true)-(Q true false-Q false false)=
      (∫x,f x*h x ∂μ)-(∫x,f x ∂μ)*(∫x,h x ∂μ) := by
  intro Q
  let z:=fun x=>(old x).part (C.fire b)
  let J:=fun (A B:Bool)=>twoBirthSettings a b A B f h
  have right (B:Bool)(x:X):J true B x b=J false B x b:=by
    cases B <;> simp [J,twoBirthSettings,Ne.symm apart]
  have da (B:Bool)(x:X):J true B x a-J false B x a=f x:=by
    cases B <;> simp [J,twoBirthSettings,apart]
  have hc (B:Bool)(x:X):J false B x b= if B then h x else 0:=by
    cases B <;> simp [J,twoBirthSettings]
  have dc (B:Bool):
      Q true B-Q false B=
        (∫x,f x*(z x+(if B then h x else 0)) ∂μ)-
        (∫x,f x ∂μ)*(∫x,z x+(if B then h x else 0) ∂μ):=by
    have row:=original_posted_covariance μ old unit (J true B) (J false B) a b apart s pair
      (right B) (admitted true B) (admitted false B)
    change Q true B-Q false B=(∫x,(J true B x a-J false B x a)*(z x+J false B x b) ∂μ)-
      (∫x,J true B x a-J false B x a ∂μ)*(∫x,z x+J false B x b ∂μ) at row
    simpa only [da,hc] using row
  have iz : Integrable z μ := by
    refine (admitted false false (C.fire b)).congr (.of_forall ?_)
    intro x
    change (postedUnit (old x) (twoBirthSettings a b false false f h x)).part (C.fire b) = z x
    rw [(unit_rows _ (unit x) _ b).2]
    simp [twoBirthSettings,z]
  have ifz : Integrable (fun x=>f x*z x) μ := by
    refine ((admitted true false s).sub (admitted false false s)).congr (.of_forall ?_)
    intro x
    change (postedUnit (old x) (J true false x)).part s - (postedUnit (old x) (J false false x)).part s=f x*z x
    rw [posted_pair_increment _ (unit x) (J true false x) (J false false x) a b apart s pair (right false x),da,hc]
    simp [z]
  rw [dc true,dc false]
  simp only [if_true, Bool.false_eq_true, if_false,add_zero]
  simp_rw [mul_add]
  have whole : Envelope (fun x => f x*h x) := Multi.Leaf.multiply fe he
  have integ {F:X→ℂ} (e:Envelope F) : Integrable F μ := by
    obtain ⟨t,ht⟩:=e.cost
    exact Integrable.of_bound e.meas.aestronglyMeasurable t (.of_forall ht)
  rw [integral_add ifz (integ whole),integral_add iz (integ he)]
  ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
