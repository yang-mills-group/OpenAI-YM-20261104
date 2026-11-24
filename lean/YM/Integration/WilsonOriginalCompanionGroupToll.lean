import YM.Integration.WilsonThermometerCorridorCash
import YM.Integration.WilsonThermometerPepperFace

/-! The original grouped bill retains every actual slot wage, including omitted slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionGroupToll
open Finset Function Lattice Wilson RG Marker MergeProof MergeProof.Ribbons
open WilsonThermometerPepperFace
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I][DecidableEq I]
def overhead (M:ℕ)(α η:ℝ)(l:ℕ):ℝ:=M*(η⁻¹*η⁻¹)*(Real.exp α)^l

theorem exact_fee (P:Rep G n)(a:I)(M l:ℕ)(η:ℝ)(w:I→ℝ)(s:Finset I)(pos:∀i,0<w i):
    (∏i∈univ\s,w i)/(WilsonThermometerWeakMixedGrouping.radius (atSite a) P M l η (fun i=>η*w i) ())=
      (overhead M (P.p.supportExponent+1/2) η l)^(Fintype.card I)/(∏i∈s,w i):=by
  let L:=atSite a
  let c:=overhead M (P.p.supportExponent+1/2) η l
  let fee:=Fibers.Salt.tow (fun i=>η*w i) (P.p.supportExponent+1/2) (η/M) l
  have all:L.contents ()=univ:=by ext i;simp [L,atSite,Fibers.contents]
  have one (i:I) : (fee i)⁻¹=c*(w i)⁻¹:=by
    dsimp only [fee,Fibers.Salt.tow,c,overhead]
    rw [mul_comm (P.p.supportExponent+1/2) _,Real.exp_nat_mul]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  have sum:(∏i∈L.contents (),fee i)⁻¹=c^(Fintype.card I)*(∏i,w i)⁻¹:=by
    rw [all,←Finset.prod_inv_distrib]
    simp only [one,Finset.prod_mul_distrib,Finset.prod_const,card_univ,Finset.prod_inv_distrib]
  have fresh:0<(∏i∈univ\s,w i):=Finset.prod_pos fun i _=>pos i
  have incumbent:0<(∏i∈s,w i):=Finset.prod_pos fun i _=>pos i
  have parts : (∏i∈univ\s,w i)*(∏i∈s,w i)=(∏i,w i):=Finset.prod_sdiff (Finset.subset_univ s)
  change (∏i∈univ\s,w i)/(∏i∈L.contents (),fee i)=c^(Fintype.card I)/(∏i∈s,w i)
  rw [div_eq_mul_inv,sum,←parts]
  field_simp [ne_of_gt fresh,ne_of_gt incumbent]

theorem restored (P:Rep G n)(a:I)(M l age:ℕ)(η H:ℝ)(w w₀:I→ℝ)(s:Finset I)
    (hot:1≤H)(yp:0<η)(pos:∀i,0<w i)(_start:∀i,0<w₀ i)
    (meter:∀i,(w i)⁻¹≤H^age*(w₀ i)⁻¹)(small:η⁻¹≤H^2)
    (quoted:Real.exp (P.p.supportExponent+1/2)≤H^6):
    (∏i∈univ\s,w i)/(WilsonThermometerWeakMixedGrouping.radius (atSite a) P M l η (fun i=>η*w i) ())≤
      ((M:ℝ)*H^(4+6*l))^(Fintype.card I)*H^(age*s.card)/(∏i∈s,w₀ i):=by
  let α:=P.p.supportExponent+1/2
  have hp:0<H:=zero_lt_one.trans_le hot
  have c : 0≤overhead M α η l:=by unfold overhead; positivity
  have hc : overhead M α η l≤(M:ℝ)*H^(4+6*l):=by
    calc _≤M*(H^2*H^2)*(H^6)^l:=by unfold overhead;gcongr
         _=(M:ℝ)*H^(4+6*l):=by rw [pow_add,pow_mul];ring
  have old:0≤(∏i∈s,w i)⁻¹:=inv_nonneg.mpr (Finset.prod_nonneg (fun i _=>(pos i).le))
  have earn:(∏i∈s,w i)⁻¹≤H^(age*s.card)*(∏i∈s,w₀ i)⁻¹:=by
    rw [←Finset.prod_inv_distrib]
    calc _ ≤ ∏i∈s,(H^age*(w₀ i)⁻¹):=Finset.prod_le_prod
             (fun i _=>(inv_pos.mpr (pos i)).le) (fun i _=>meter i)
         _ = _:=by rw [Finset.prod_mul_distrib,prod_const,Finset.prod_inv_distrib,pow_mul]
  rw [exact_fee P a M l η w s pos]
  rw [div_eq_mul_inv (_^_) (∏i∈s,w i),div_eq_mul_inv (_*_) (∏i∈s,w₀ i),mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ c hc _) earn old (pow_nonneg (c.trans hc) _)

end YM.Integration.WilsonOriginalCompanionGroupToll
end
