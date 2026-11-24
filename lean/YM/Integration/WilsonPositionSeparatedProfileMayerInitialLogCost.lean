import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogIncome
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogReserve

/-! A fixed exponent per physical mark pays both the connected log error and its entire
independently filed thermal Taylor remainder. All inputs are for one normalized field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCost
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open Extra.Trajectories (connected)
open WilsonPositionSeparatedProfileMayerInitialLogBill
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

theorem purchased {n q E:ℕ} {g C B:ℝ} (pos:0<g) (small:g≤1) (cp:0≤C) (bp:0≤B)
    {x:Grade Γ n} (lead:UnitLeading x) (sym:Symmetric x)
    (F:Poly Γ) (quiet:F.part Γ.quiet≠0) (w:V→ℝ) (hw:∀i,0<w i)
    (incoming:entire w (render (ratio x))≤C/g^E)
    (reserve:q+E*Fintype.card V≤n)
    (raw:Poly.price w (unitScale F-value (g:ℂ) (ratio x))≤B*g^(q+E*Fintype.card V+1)):
    Poly.price w (connected (unitScale F)-value (g:ℂ) (logMarked x))≤
      g^(q+1)*((B+1)*(Fintype.card V)*(1+C+B)^(Fintype.card V)):=by
  let a:=Fintype.card V
  let A:=1+C+B
  let M:=A/g^E
  let P:=value (g:ℂ) (ratio x)
  have fund:1≤A:=by dsimp [A];linarith
  have gp:0<g^E:=pow_pos pos _
  have gb:g^E≤1:=pow_le_one₀ pos.le small
  have hnorm:‖(g:ℂ)‖=g:=by simp [abs_of_pos pos]
  have Pp:Poly.price w P≤C/g^E:=
    (WilsonPositionSeparatedProfileMayerInitialLogIncome.value (ratio x) w hw (g:ℂ)
      (hnorm.le.trans small)).trans incoming
  have account:1+C/g^E+B≤M:=by
    apply (le_div_iff₀ gp).2
    calc
      _=(1+B)*g^E+C:=by field_simp;ring
      _≤(1+B)*1+C:=by gcongr
      _=A:=by dsimp [A];ring
  have scaled:1+C/g^E≤M:=by linarith
  have pp:Poly.price w (1-P)≤1+C/g^E:=by
    calc
      _≤Poly.price w (1:Poly Γ)+Poly.price w P:=priced_sub w hw 1 P
      _=1+Poly.price w P:=by rw [Poly.one_price]
      _≤_:=by linarith
  have same:Poly.price w (P-unitScale F)=Poly.price w (unitScale F-P):=by
    rw [←priced_neg w (P-unitScale F),neg_sub]
  have prior:Poly.price w (unitScale F-P)≤B:=raw.trans
    (mul_le_of_le_one_right bp (pow_le_one₀ pos.le small))
  have field:Poly.price w (1-unitScale F)≤M:=by
    calc
      _=Poly.price w ((1-P)+(P-unitScale F)):=by congr 1;abel
      _≤Poly.price w (1-P)+Poly.price w (P-unitScale F):=Poly.addition hw _ _
      _≤M:=by rw [same];exact (add_le_add pp prior).trans account
  have bill:=log_mark_pay lead sym (g:ℂ) (z:=1) (hnorm.le.trans small) a
    (fun _=>Finset.card_le_univ _) F quiet w hw field (pp.trans scaled) raw
  have tail:subtotal w n 1 (logSeries (a+n) (render (ratio x)))≤∑i∈range a,M^(i+1):=by
    refine (WilsonPositionSeparatedProfileMayerInitialLogBill.tail lead w hw (C/g^E) incoming).trans ?_
    exact Finset.sum_le_sum fun i _=>pow_le_pow_left₀ (by positivity) scaled _
  have old:= (WilsonPositionSeparatedProfileMayerInitialLogReserve.budget pos small fund
    (le_refl (q+E*a))).1
  have full:=(WilsonPositionSeparatedProfileMayerInitialLogReserve.budget pos small fund reserve).2
  rw [hnorm] at bill
  calc
    _≤repeats a M*(B*g^(q+E*a+1))+g^(n+1)*(∑i∈range a,M^(i+1)):=
      bill.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left tail (pow_nonneg pos.le _)))
    _=B*(g^(q+E*a+1)*repeats a M)+g^(n+1)*(∑i∈range a,M^(i+1)):=by ring
    _≤B*(g^(q+1)*(a*A^a))+g^(q+1)*(a*A^a):=add_le_add (mul_le_mul_of_nonneg_left old bp) full
    _=g^(q+1)*((B+1)*(Fintype.card V)*(1+C+B)^(Fintype.card V)):=by dsimp [A,a];ring

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCost
