import YM.Integration.WilsonOriginalMicroscopicEntranceDeposits
import YM.Integration.WilsonThermometerSolitaryExchange

/-! The two actual time-separated portfolios are heard at one field. Each
ordered difference has precisely the two proper companions of its date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceExchange
open Finset MeasureTheory Lattice Wilson RG OPE.Therm Marker MergeProof.Accent Extra.Trajectories
open WilsonThermometerSolitaryExchange (word share factor)
open WilsonOriginalMicroscopicEntranceDeposits (mean reading)
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

theorem word_value (x:Fin 3 → ℂ)(s:(J).Mode):(word x).part s=∏a∈s.val,x a:=by
  let term (a:Fin 3):Poly J:=Poly.send ((J).fire a) (x a)
  have zero(a:Fin 3):(term a).part (J).quiet=0:=by simp [term,Poly.part_send,Ne.symm ((J).fire_hot _)]
  have atom(a:Fin 3):Poly.pass (term a)=factor a (x a):=
    pass_send (show ((J).fire a).val.Nonempty from singleton_nonempty _) _
  have full:Poly.pass (∑a,term a)=word x:=by
    rw [Fin.sum_univ_three,pass_add (by rw [Poly.part_plus,zero,zero,zero_add]) (zero 2),
      pass_add (zero 0) (zero 1),atom,atom,atom]
    rfl
  rw [←full]
  exact Extra.Trajectories.pass_fire x s

theorem original {G:Gauge}(C:Family G)(hC:C.Makes){N p K f:ℕ}(live:K ≤ N)(stop:f ≤ K)
    (A:Fin 3 → Config G (C.side N p) → ℂ)(B:Fin 3 → Config G (C.side K p) → ℂ)
    (one:∀a,WilsonOriginalMicroscopicEntranceDeposits.funded (A a))
    (two:∀a,WilsonOriginalMicroscopicEntranceDeposits.funded (B a))(s:(J).Mode)(W:Config G (C.side f p)):
    let x:=fun a=>mean C N (A a) f W
    let y:=fun a=>mean C N (B a) f W
    actualTransport C (N:=N) (fun U=>∏a∈s.val,A a U) (stop.trans live) W-
      actualTransport C (N:=N) (fun U=>∏a∈s.val,B a U) stop W=
      ((∑i∈Ico f N,reading C N A s.val f i W)-(∑i∈Ico f K,reading C N B s.val f i W))+
        ∑a,(x a-y a)*share x y a s:=by
  intro x y
  have first:=WilsonOriginalMicroscopicEntranceDeposits.original C N A s.val hC one le_rfl (stop.trans live) W
  have second:=WilsonOriginalMicroscopicEntranceDeposits.original C N B s.val hC two live stop W
  rw [←first,←second,←WilsonThermometerSolitaryExchange.ordinary,word_value,word_value]
  dsimp only [WilsonOriginalMicroscopicEntranceDeposits.singles,x,y]
  ring

end YM.Integration.WilsonOriginalMicroscopicEntranceExchange
end
