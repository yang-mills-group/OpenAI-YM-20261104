import YM.Integration.WilsonThermometerReceivedHardErasure
import YM.Integration.WilsonMeasuredCompanionFace

/-! Ordered replacement of the three actual singleton numerators, including the spent hard terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryExchange
open Finset Marker MergeProof.Accent Extra.Trajectories
open scoped BigOperators Classical

local notation "J" => Stock.census (Fin 3)

/-- The occupied generator for the already named seat. -/
def token (v:Fin 3):Poly (J):=Poly.send ((J).fire v) 1

def factor (v:Fin 3)(c:ℂ):Poly (J):=1+Poly.send ((J).fire v) c

def word (a:Fin 3→ℂ):Poly (J):=factor 0 (a 0)*factor 1 (a 1)*factor 2 (a 2)

/-- The first slots have already been replaced.  Later slots retain their original values. -/
def peer (a b:Fin 3→ℂ)(v:Fin 3):Poly (J):=
  ![factor 1 (a 1)*factor 2 (a 2),factor 0 (b 0)*factor 2 (a 2),factor 0 (b 0)*factor 1 (b 1)] v

def share (a b:Fin 3→ℂ)(v:Fin 3)(s:(J).Mode):ℂ:=(peer a b v*token v).part s

theorem factor_change (v:Fin 3)(c d:ℂ):
    factor v c-factor v d=Poly.bead (J) (c-d)*token v:=by
  rw [Poly.product_bead]
  ext1 s
  simp only [factor,sub_eq_add_neg,Poly.part_plus,Poly.part_neg,Poly.part_smul,token,Poly.part_send]
  split_ifs <;> ring

theorem ordinary (a b:Fin 3→ℂ)(s:(J).Mode):
    (word a).part s-(word b).part s=∑v,(a v-b v)*share a b v s:=by
  have h:word a-word b=∑v,(factor v (a v)-factor v (b v))*peer a b v:=by
    simp [word,peer,Fin.sum_univ_three];ring
  have p:=congrArg (fun z:Poly (J)=>z.part s) h
  simp only [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,Poly.part_sum] at p
  rw [sub_eq_add_neg,p]
  apply sum_congr rfl
  intro v _
  rw [←sub_eq_add_neg,factor_change,mul_assoc,Poly.product_bead,Poly.part_smul]
  simp [share,mul_comm]

/-- The complete hard surplus on a face after the paid erasure. -/
def spent (vac:ℂ)(a:Fin 3→ℂ)(D:Poly (J))(s:(J).Mode):ℂ:=D.part s-vac*(word a).part s

/-- Precisely the occupied hard contribution to one original singleton. -/
def single (vac:ℂ)(a:Fin 3→ℂ)(D:Poly (J))(v:Fin 3):ℂ:=D.part ((J).fire v)-vac*a v

theorem original (vac:ℂ)(a b:Fin 3→ℂ)(D F:Poly (J))(h:Fin 3→ℂ)
    (measured:∀v,h v=D.part ((J).fire v)-F.part ((J).fire v))(s:(J).Mode):
    D.part s-F.part s=spent vac a D s-spent vac b F s+
      ∑v,(h v-(single vac a D v-single vac b F v))*share a b v s:=by
  have fixed:∀v,h v-(single vac a D v-single vac b F v)=vac*(a v-b v):=by
    intro v
    rw [measured]
    unfold single
    ring
  simp only [fixed,mul_assoc,←mul_sum,←ordinary,spent]
  ring

end YM.Integration.WilsonThermometerSolitaryExchange
