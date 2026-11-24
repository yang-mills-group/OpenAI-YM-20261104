import YM.Integration.WilsonMaxwellThermometerNominatedDelta
import YM.Integration.WilsonThermometerCenteredBound

/-! Six signed ordinary differences suffice for the first-slope remainder.
The unpriced full physical difference contributes identically zero to every
proper residual, even after division by the common filed Maxwell table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedDeltaProper
open Finset Filter Marker QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonMaxwellThermometerNominatedDelta
open private annihilates from YM.Integration.WilsonThermometerCenteredAlgebra
open scoped BigOperators Classical Topology
local notation "J" => Stock.census (Fin 3)

def trim (F:Poly J):Poly J:=F-Poly.send full (F.part full)

private theorem bill (F:Poly J):rent (trim F)≤rent F:=by
  unfold rent Poly.price
  apply Finset.sum_le_sum
  intro s _
  by_cases h:s=full
  · subst s;simp [trim,sub_eq_add_neg,Poly.part_send,Poly.toll]
  · simp [trim,sub_eq_add_neg,Poly.part_send,h,Poly.toll]

private theorem delta (F G:Poly J):proper F-proper G=trim (F-G):=by
  ext s
  by_cases h:s=full <;> simp [proper,trim,sub_eq_add_neg,Poly.part_send,h]

private theorem billed (F:Poly J) (z:ℂ):trim (F+Poly.send full z)=trim F:=by
  ext s
  by_cases h:s=full
  · subst s;simp [trim,sub_eq_add_neg,Poly.part_send]
  · simp [trim,sub_eq_add_neg,Poly.part_send,h]

private theorem top (W:Poly J) (wp:W.part (J).quiet=1) (z:ℂ):
    Poly.send full z*inverseMass W=Poly.send full z:=by
  have unit: (inverseMass W).part (J).quiet=1:=by
    have h:=congrArg (fun (P:Poly J)=>P.part (J).quiet) (right_inverse wp)
    simpa only [Poly.quiet_mul,wp,one_mul,Poly.one_part,if_pos rfl,if_true] using h
  have q:(inverseMass W-1).part (J).quiet=0:=by simp [sub_eq_add_neg,unit]
  have t:=annihilates (inverseMass W-1) q z
  rw [sub_mul,one_mul] at t
  exact (mul_comm _ _).trans (sub_eq_zero.mp t)

theorem removed (F G W:Poly J) (wp:W.part (J).quiet=1):
    residue F W-residue G W=trim (trim (F-G)*inverseMass W):=by
  rw [residue,residue,delta]
  unfold total
  rw [←sub_mul]
  have split:F-G=trim (F-G)+Poly.send full ((F-G).part full):=(sub_add_cancel ..).symm
  conv_lhs=>rw [split,add_mul,top W wp,billed]

theorem spent (F G W:Poly J) (wp:W.part (J).quiet=1):
    rent (residue F W-residue G W)≤rent (trim (F-G))*rent (inverseMass W):=by
  rw [removed F G W wp]
  exact (bill _).trans (Poly.multiplication (fun _:Fin 3=>zero_lt_one) _ _)

theorem self (W:Poly J) (wp:W.part (J).quiet=1):residue W W=0:=by
  have h:full≠(J).quiet:=by intro e; exact univ_nonempty.ne_empty (congrArg Subtype.val e : (univ:Finset (Fin 3))=∅)
  simp [residue,total,right_inverse wp,proper,Poly.one_part,h]

theorem six (F G:Poly J) (z:ℝ) (pos:0≤z) (u:F.part (J).quiet=G.part (J).quiet)
    (signed:∀s:(J).Mode,s≠(J).quiet→s≠full→‖F.part s-G.part s‖≤z):
    rent (trim (F-G))≤8*z:=by
  unfold rent Poly.price
  calc
    _≤∑s:(J).Mode,z:=by
      refine Finset.sum_le_sum fun s _=>?_
      by_cases a:s=full
      · subst s;simpa [trim,Poly.toll,sub_eq_add_neg,Poly.part_send] using pos
      by_cases b:s=(J).quiet
      ·
          subst s
          simpa [trim,Poly.toll,sub_eq_add_neg,Poly.part_send,a,u] using pos
      · simpa [trim,Poly.toll,sub_eq_add_neg,Poly.part_send,a] using signed s b a
    _=_:=by
      have n:Fintype.card (J).Mode=8:=by decide
      rw [Finset.sum_const,Finset.card_univ,n,nsmul_eq_mul]
      norm_num

end YM.Integration.WilsonMaxwellThermometerNominatedDeltaProper
