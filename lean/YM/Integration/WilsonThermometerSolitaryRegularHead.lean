import YM.Integration.WilsonThermometerMixedGallery
import YM.Integration.WilsonThermometerSolitaryLampReading
import YM.Integration.WilsonThermometerSolitaryVacuumOpponent

/-! On the original quiet hard gas, erasing every multiply occupied log row
leaves exactly the product of the original three ordinary singleton fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryRegularHead
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Extra.Trajectories
open WilsonThermometerMixedGallery WilsonThermometerMixedAmplitude
open WilsonThermometerSolitaryFiledExchange WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{I X:Type}{p:BudgetPoint}{o:Fin 3→Site n}{W:Rep G n}

abbrev dyed (c:ℂ)(L:Lamps X I G p o (J)):=lamps c (fun _ _=>True) L

theorem coordinate (c:ℂ)(L:Lamps X I G p o (J))(x:X)(U:Config G n)
    (seats:Summable (fun i=>L.frame i x U))(lo:Summable (fun i=>(dyed c L).frame i x U))(s:(J).Mode):
    ((dyed c L).log x U).part s=rent c (fun _=>True) s*(L.log x U).part s:=by
  change (∑'i,(dyed c L).frame i x U).part s=rent c (fun _=>True) s*(∑'i,L.frame i x U).part s
  rw [Poly.share lo,Poly.share seats,←tsum_mul_left]
  apply tsum_congr
  intro i
  rw [sheet];rfl

theorem erased (L:Lamps X I G p o (J))(x:X)(U:Config G n)
    (seats:Summable (fun i=>L.frame i x U))(lo:Summable (fun i=>(dyed 0 L).frame i x U)):
    Poly.pass ((dyed 0 L).log x U)=word (fun v=>(L.log x U).part ((J).fire v)):=by
  have empty:∀s:(J).Mode,s.val.card≠1→((dyed 0 L).log x U).part s=0:=by
    intro s few
    by_cases no:s.val.card=0
    · have eq:s=(J).quiet:=Subtype.ext (Finset.card_eq_zero.mp no)
      subst s
      exact (dyed 0 L).quiet_of_hasSum x U lo
    · have multi:1<s.val.card:=by omega
      rw [coordinate 0 L x U seats lo s,show rent 0 (fun _=>True) s=0 from if_pos ⟨multi,trivial⟩,zero_mul]
  rw [WilsonThermometerSolitaryLampReading.sparse _ empty]
  congr 1
  funext v
  rw [coordinate 0 L x U seats lo]
  have few:((J).fire v).val.card=1:=card_singleton v
  change rent 0 (fun _=>True) ((J).fire v)*(L.log x U).part _=(L.log x U).part _
  rw [show rent 0 (fun _=>True) ((J).fire v)=1 from if_neg (by omega),one_mul]

abbrev endpoint (c:ℂ)(A:Gallery X I o W (J)):=WilsonThermometerSolitaryVacuumOpponent.offer (dyed c A.E) A

theorem original (A:Gallery X I o W (J)){T q:ℂ}(inverse:q*T=1)(w:Fin 3→ℝ)(wp:∀v,0<w v)
    {e e₀ eT k:ℝ}(base:A.E.Paid w W.p.B W.p.supportExponent e)
    (cut:(dyed 0 A.E).Paid w W.p.B W.p.supportExponent e₀)
    (raised:(dyed T A.E).Paid w W.p.B W.p.supportExponent eT)(old:A.K.Paid w W.p.B W.p.supportExponent k)
    (x:X)(U:Config G n)(s:(J).Mode):
    WilsonThermometerSolitaryFiledExchange.mixed A x U s=q*(((endpoint T A).density x U).part s-
      ((endpoint 0 A).density x U).part s):=by
  have lo:=cut.sums W.p.exponent_pos.le wp x U
  have hi:=raised.sums W.p.exponent_pos.le wp x U
  have actual:=base.sums W.p.exponent_pos.le wp x U
  have series:Line q ((dyed 0 A.E).log x U) (A.E.log x U) ((dyed T A.E).log x U):=by
    apply WilsonThermometerMixedAmplitude.series _ _ _ lo hi
    intro i
    change Line q ((lamps 0 (fun _ _=>True) A.E).frame i x U) _ ((lamps T (fun _ _=>True) A.E).frame i x U)
    rw [sheet,sheet]
    exact amplitude _ _ inverse
  obtain ⟨_,low⟩:=WilsonThermometerSolitaryVacuumOpponent.original (dyed 0 A.E) A w wp old
  obtain ⟨_,high⟩:=WilsonThermometerSolitaryVacuumOpponent.original (dyed T A.E) A w wp old
  have read:=congrArg (fun z:Poly (J)=>z.part s) (passed series).value
  change (Poly.pass (A.E.log x U)).part s=(Poly.pass ((dyed 0 A.E).log x U)).part s+
    q*((Poly.pass ((dyed T A.E).log x U)).part s-(Poly.pass ((dyed 0 A.E).log x U)).part s) at read
  unfold WilsonThermometerSolitaryFiledExchange.mixed value endpoint
  rw [high x U,low x U,←erased A.E x U actual lo,Poly.part_smul,Poly.part_smul,read]
  ring

end YM.Integration.WilsonThermometerSolitaryRegularHead
