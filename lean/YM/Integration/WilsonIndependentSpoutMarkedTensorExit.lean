import YM.Integration.WilsonIndependentSpoutPostedMarkLaw

/-! Every retained angular tensor of the normalized finite marked ratio, including its scalar. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMarkedTensorExit
open Function PowerSeries Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer PertExtension
open WilsonCoeffUV.Power WilsonCoeffUV.Blue.Cameo
open WilsonIndependentConditionalRawSpout (finite)
open WilsonIndependentSpoutFiniteExitRows (pulled withdrawn)
open scoped BigOperators Classical Matrix
variable {X I J:Type}[Fintype X][Fintype I][Fintype J]

theorem measured (D:Matrix X (I⊕J) ℝ)(C:Matrix I I ℝ)(sym:C.transpose=C)
    {P W:Pal ℝ X}{B:Pal ℝ J}{k p:ℕ}(ps:shellK 2 P)(pz:P 0=0)(pp:∀e,Pure (P e))
    (ws:shellK k W)(wp:∀e,Pure (W e))(bs:shellK k B)(bp:∀e,Pure (B e))(β:Cost)
    (paid:Equal (p+1) (Wick J C (raiseE (loom D (flash P))*loom D (flash W)))
      (Wick J C (raiseE (loom D (flash P)))*redo β (flash B))):
    ∀e≤p,pulled D (finite (D*fillSlots J C*D.transpose) P W k) e=mix β B e:=by
  let K:=D*fillSlots J C*D.transpose
  let E:=finite K P W k
  have exp:=WilsonIndependentSpoutPostedMarkLaw.expense K ps pz ws wp
  have pure0:constantCoeff (loom D (flash P))=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,loom,coeff_map,flash,coeff_mk,pz]
    simp [totalR]
  have funded:IsUnit (Wick J C (raiseE (loom D (flash P)))):=
    PowerSeries.isUnit_iff_constantCoeff.mpr ((glaze_log C pure0) ▸ isUnit_one)
  have actual:=WilsonIndependentSpoutAmbientMark.projected D C sym ps pz pp ws wp
  rw [actual] at paid
  have take:=WilsonIndependentSpoutPostedMarkLaw.cancel funded paid
  rw [withdrawn D E exp.1,redo_stern β bs] at take
  intro e he
  change pulled D E e=mix β B e
  have fin:FiniteGen (pulled D E e):=fade_finite (fade_finite (exp.1 e) D) _
  have symm:Pure (pulled D E e):=fade_pure (fade_pure (exp.2 e) D) _
  apply gen_inj fin (finite_shell (mix_length (A:=β) bs) e) symm (mix_pure bp e)
  simpa only [flash,coeff_mk] using take e (by omega)

end YM.Integration.WilsonIndependentSpoutMarkedTensorExit
