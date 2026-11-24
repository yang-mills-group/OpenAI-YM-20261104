import YM.SchemeRG11.Cover.Breathe
/-! Scalar-base-change for symbols (ordinary, no conjugated slots). -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial
open scoped Classical
variable {R S J I B : Type*} [CommRing R] [CommRing S]
lemma transformV (F:R→+*S)(p:Paper I R) (z:I→R): vent (fun i=>F (z i)) (map F p)=map F (vent z p):=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [map_C,vent_C,vent_C,map_zero]
 | add a b ha hb=> rw [_root_.map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a i h=> rw [map_mul (map F),map_X,vent_x,vent_x,map_add,MvPolynomial.smul_eq_C_mul,MvPolynomial.smul_eq_C_mul,map_mul (map F),map_mul (map F),map_C, map_X,h]
namespace Dose
variable (D:Dose I R) (F : R→+* S)
def mapped : Dose I S:=⟨fun i j=> F (D.pulse i j),fun i j=>by rw [D.beats i j]⟩
lemma mapped_heat (p:Paper I R) : (D.mapped F).heat (map F p) = map F (D.heat p):=by
 induction p using MvPolynomial.induction_on with
 | C=> rw [map_C,heat_C,D.heat_C,map_C]
 | add a b ha hb=> rw [map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a i ih=>
   rw [map_mul (map F),map_X,heat_x,D.heat_x, map_add,map_mul (map F),map_X, ih]
   congr 1; apply transformV
lemma mapped_neg : (D.mapped F).neg=D.neg.mapped F:=by unfold mapped neg; congr; funext i j; rw [map_neg]
lemma mapped_avg (p:Paper I R): (D.mapped F).avg (MvPolynomial.map F p)= F (D.avg p):=by
 rw [avg_def,mapped_heat,D.avg_def]; generalize D.heat p=q
 induction q using MvPolynomial.induction_on with
 | C c=> rw [map_C,aeval_C,aeval_C];rfl
 | add a b ha hb=> simp only [_root_.map_add,ha,hb]
 | mul_X p i h => rw [map_mul (map F),map_X, map_mul (aeval _),aeval_X,map_mul (aeval _), aeval_X,mul_zero,mul_zero,map_zero]
end Dose
end YM.SchemeRG11.Haze
