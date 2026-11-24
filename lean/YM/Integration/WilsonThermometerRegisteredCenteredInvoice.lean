import YM.Integration.WilsonThermometerRegisteredSingletonCenter
import YM.Integration.WilsonThermometerRegisteredRestrictedWithdrawal

/-! Two affordable real source submissions implement the exact signed three-field difference. The common multiplier reads no full three-field coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredInvoice
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar WilsonThermometerRegisteredSingletonCenter
open WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def properInvoice (F Q:Poly J):Poly J:=invoice F Q-Poly.send full ((invoice F Q).part full)
def restoration (w:Fin 3→ℝ) (F Q:Poly J):ℝ:=2*(1+Poly.price w (properInvoice F Q-1))
def extra (w:Fin 3→ℝ) (F Q:Poly J):Poly J:=(((restoration w F Q)⁻¹:ℝ):ℂ) • (properInvoice F Q-1)
def tested (w:Fin 3→ℝ) (F Q:Poly J):Poly J:=inverseMass (1+extra w F Q)

private theorem proper_unit (F Q:Poly J) (qu:Q.part (J).quiet=1):(properInvoice F Q).part (J).quiet=1:=by
  change (invoice F Q).part (J).quiet-(Poly.send full ((invoice F Q).part full)).part (J).quiet=1
  rw [invoice_unit F Q qu,Poly.part_send,if_neg (show (J).quiet≠full by decide),sub_zero]

private theorem correction_top (e:Fin 3→ℂ):(correction e).part full=0:=by
  change (1:Poly J).part full-(Poly.send (face {0}) (e 0)).part full-(Poly.send (face {1}) (e 1)).part full-
    (Poly.send (face {2}) (e 2)).part full+(Poly.send (face {1,2}) (2*e 1*e 2)).part full=0
  simp only [Poly.one_part,if_neg (show full≠(J).quiet by decide),Poly.part_send,if_neg (show full≠face {0} by decide),
    if_neg (show full≠face {1} by decide),if_neg (show full≠face {2} by decide),if_neg (show full≠face {1,2} by decide),sub_zero,add_zero]

open private annihilates from YM.Integration.WilsonThermometerCenteredAlgebra

theorem proper (F Q:Poly J) (fu:F.part (J).quiet=1) (qu:Q.part (J).quiet=1):
    read (Extra.Trajectories.connected F) univ-read (Extra.Trajectories.connected Q) univ=
      ((F-Q)*properInvoice F Q).part full:=by
  have blank:(F-Q).part (J).quiet=0:=by change F.part _-Q.part _=0;rw [fu,qu,sub_self]
  have seen:(Q*invoice F Q).part full=0:=by rw [invoice,←mul_assoc,right_inverse qu,one_mul,correction_top]
  rw [cell F Q fu qu,total,restored F Q qu,properInvoice,mul_sub,annihilates _ blank,sub_zero,sub_mul]
  change _=(F*invoice F Q).part full-(Q*invoice F Q).part full
  rw [seen,sub_zero]

variable (w:Fin 3→ℝ) (F Q:Poly J)

theorem charge (qu:Q.part (J).quiet=1):
    restoration w F Q=2*(1+∑ s:(J).Mode with s≠full ∧ s≠(J).quiet,Poly.toll w s*‖(invoice F Q).part s‖):=by
  have eq (s:(J).Mode):((properInvoice F Q-1):Poly J).part s=
      if s≠full ∧ s≠(J).quiet then (invoice F Q).part s else 0:=by
    change ((invoice F Q).part s-(Poly.send full ((invoice F Q).part full)).part s)-(1:Poly J).part s=_
    rw [Poly.part_send,Poly.one_part]
    by_cases top:s=full
    · subst s;simp [show full≠(J).quiet by decide]
    · by_cases zero:s=(J).quiet
      · subst s;simp [top,invoice_unit F Q qu]
      · simp [top,zero]
  unfold restoration Poly.price
  rw [Finset.sum_filter]
  congr 3
  funext s
  rw [eq];split <;> simp_all

theorem positive (prices:∀v,0<w v):0<restoration w F Q:=by
  have h:=Poly.nonnegative (R:=J) prices (properInvoice F Q-1)
  unfold restoration;linarith

theorem inverse (qu:Q.part (J).quiet=1):inverseMass (tested w F Q)=1+extra w F Q:=by
  apply twice
  change (1:Poly J).part (J).quiet+(extra w F Q).part (J).quiet=1
  rw [Poly.one_part,if_pos rfl,extra,Poly.part_smul]
  change 1+_ * ((properInvoice F Q).part (J).quiet-(1:Poly J).part (J).quiet)=1
  rw [proper_unit F Q qu,Poly.one_part,if_pos rfl,sub_self,mul_zero,add_zero]

theorem affordable (prices:∀v,0<w v) (qu:Q.part (J).quiet=1):
    Poly.price w (inverseMass (1:Poly J))≤fee J ∧ Poly.price w (inverseMass (tested w F Q))≤fee J:=by
  have good:=positive w F Q prices
  have modest:Poly.price w (extra w F Q)≤(2:ℝ)⁻¹:=by
    rw [extra,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr good),inv_mul_eq_div,div_le_iff₀ good]
    unfold restoration;linarith
  have budget:=Poly.addition prices (1:Poly J) (extra w F Q)
  rw [Poly.one_price] at budget
  have reserve:=WilsonThermometerRegisteredFaceTable.room_two
  rw [WilsonThermometerRegisteredFaceTable.unit,inverse w F Q qu,Poly.one_price]
  exact ⟨by linarith,by linarith⟩

/-- This equality holds for an arbitrary submitted numerator. The constant weights
can therefore be taken outside the actual older integration. -/
theorem reading (prices:∀v,0<w v) (qu:Q.part (J).quiet=1) (X:Poly J):
    (X*properInvoice F Q).part full=
      (restoration w F Q:ℂ)*(total X (tested w F Q)).part full+
        (1-(restoration w F Q:ℂ))*(total X 1).part full:=by
  have gap:((restoration w F Q:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt (positive w F Q prices))
  rw [total,total,inverse w F Q qu,WilsonThermometerRegisteredFaceTable.unit,mul_one,
    mul_add,mul_one,extra,mul_smul_comm,mul_sub,mul_one,Poly.part_plus,Poly.part_smul]
  change _=(restoration w F Q:ℂ)*(X.part full+(((restoration w F Q)⁻¹:ℝ):ℂ)*
    ((X*properInvoice F Q).part full-X.part full))+(1-(restoration w F Q:ℂ))*X.part full
  rw [Complex.ofReal_inv];field_simp;ring

theorem original (prices:∀v,0<w v) (fu:F.part (J).quiet=1) (qu:Q.part (J).quiet=1):
    read (Extra.Trajectories.connected F) univ-read (Extra.Trajectories.connected Q) univ=
      (restoration w F Q:ℂ)*(total (F-Q) (tested w F Q)).part full+
        (1-(restoration w F Q:ℂ))*(total (F-Q) 1).part full:=
  (proper F Q fu qu).trans (reading w F Q prices qu (F-Q))

end YM.Integration.WilsonThermometerRegisteredCenteredInvoice
