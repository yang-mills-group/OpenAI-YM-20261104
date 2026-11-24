import YM.Integration.WilsonThermometerSolitaryFiledExchange
import YM.Integration.WilsonPrecontactSeparatedLamps

/-! Exact ordinary reading after taking the surviving singleton lamps on their actual masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryLampReading
open Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Earn Extra.Trajectories Next.Rank.Exponential
open WilsonThermometerSolitaryExchange WilsonThermometerSolitaryFiledExchange
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge} {n:Side} {W:Rep G n} {o:Fin 3→Site n} {T I:Type}

theorem sparse (a:Poly (J))(supported:∀s:(J).Mode,s.val.card≠1→a.part s=0):
    Poly.pass a=word (fun v=>a.part ((J).fire v)):=by
  let one (v:Fin 3):Poly (J):=Poly.send ((J).fire v) (a.part ((J).fire v))
  have inject (i j:Fin 3):((J).fire i=(J).fire j)↔i=j:=by
    constructor
    · intro h
      exact singleton_inj.mp (congrArg Subtype.val h)
    · exact congrArg _
  have total:a=∑v,one v:=by
    ext1 s
    rw [Poly.part_sum]
    by_cases h:s.val.card=1
    · obtain ⟨v,hv⟩:=Finset.card_eq_one.mp h
      have eq:s=(J).fire v:=Subtype.ext hv
      subst s
      simp [one,Poly.part_send,inject]
    · have no(v:Fin 3):s≠(J).fire v:=by
        intro hv
        apply h
        rw [hv]
        exact card_singleton v
      simp [one,Poly.part_send,no,supported s h]
  have quiet (v:Fin 3):(one v).part (J).quiet=0:=by simp [one,Poly.part_send,Ne.symm ((J).fire_hot _)]
  have nil(v:Fin 3):Poly.pass (one v)=factor v (a.part ((J).fire v)):=by
    exact pass_send (show ((J).fire v).val.Nonempty from singleton_nonempty _) _
  calc
    _ = Poly.pass (one 0+one 1+one 2):=by rw [←Fin.sum_univ_three,total]
    _ = _ :=by rw [pass_add (by rw [Poly.part_plus,quiet,quiet,zero_add]) (quiet 2),
        pass_add (quiet 0) (quiet 1),nil,nil,nil];rfl

theorem original (A:Gallery T I o W (J))(solitary:∀i,(A.E.mode i).val.card=1)(x:T)(U:Config G n)
    (seats:Summable (fun i=>A.E.frame i x U))(s:(J).Mode):mixed A x U s=0:=by
  have render:Poly.pass (A.E.log x U)=word (value A.E x U):=by
    apply sparse
    intro t ht
    change (∑'i,A.E.frame i x U).part t=0
    rw [Poly.share seats t]
    have off (i:I):(A.E.frame i x U).part t=0:=by
      change (Poly.send (A.E.mode i) _).part t=0
      rw [Poly.part_send,if_neg]
      exact fun h=>ht (h ▸ solitary i)
    simp [off]
  rw [mixed,render,sub_self,mul_zero]

end YM.Integration.WilsonThermometerSolitaryLampReading
