import YM.Integration.WilsonMeasuredOriginalPeriodRead

/-! On the original period, copying a formal group word changes its binder
paths while preserving the center, mark, scalar and whole raw sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOriginalPeriodWord
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 FVA1Physical.TwoReset AllOrder AllOrder.Floe
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V I X:Type}[DecidableEq V]
    {P:Passport n V}{J:Census V}(M:I→Row P J G X)(w:V→ℕ)
    (q:I→ℂ)(L:Layout G)(tape:Finset Age)

theorem marked (h:Multi.Hot J) :
    (copyColor (f:=n) dvd_rfl M w q L tape).mark h=(Air.craft M q w L tape).mark h := by
  classical
  have count: Pages n n=1:=by simp [Pages,Nat.div_self n.pos]
  let home:Fin (Pages n n):=⟨0,by omega⟩
  have unique (u:Fin (Pages n n)):u=home:=by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (by have:=u.isLt;change u.val≤0;omega)
  unfold copyColor
  change (∑ u : Fin (Pages n n), (Air.craft (fun j=>FVA1Physical.TwoReset.copy dvd_rfl (M j) u) q w L tape).mark h) = _
  rw [Finset.sum_eq_single home]
  · funext g U
    unfold Air.craft Fk.grant Air.sums
    apply tsum_congr
    intro i
    have same:(ScatterR.actor (fun j=>FVA1Physical.TwoReset.copy dvd_rfl (M j) home) i).val =
        (ScatterR.actor M i).val:=rfl
    dsimp only
    by_cases active:(ScatterR.actor M i).val=h.val
    · have yes:(ScatterR.actor (fun j=>FVA1Physical.TwoReset.copy dvd_rfl (M j) home) i).val=h.val:=same.trans active
      rw [if_pos yes,if_pos active]
      unfold ScatterR.familyAt
      rw [recenter,WilsonMeasuredOriginalPeriodRead.atSite]
      rfl
    · have no:(ScatterR.actor (fun j=>FVA1Physical.TwoReset.copy dvd_rfl (M j) home) i).val≠h.val:=fun eq=>active (same.symm.trans eq)
      rw [if_neg no,if_neg active]
  · intro u _ other
    exact (other (unique u)).elim
  · simp

theorem literal (t:X)(j:ℕ)(A:Stationary.Link G n) :
    peek (f:=n) dvd_rfl M w L tape t j A =
      Air.discharge (Air.craft M (fun i=>(M i).paint t) w L tape) j (Stationary.arm G n 1 A) := by
  unfold peek Air.discharge
  apply congrArg (Multi.lit J)
  funext h
  rw [marked]
  rfl

end YM.Integration.WilsonMeasuredOriginalPeriodWord
end
