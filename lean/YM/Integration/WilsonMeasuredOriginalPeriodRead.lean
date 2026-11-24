import YM.Integration.FVA1Physical.TwoReset.ReadCopies

/-! At the original period a formal copied probe has one page. Its centered
word is evaluated at the same group site, with the original row and price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOriginalPeriodRead
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical.TwoReset
open AllOrder AllOrder.Floe
open scoped BigOperators Classical

theorem identity (n:Side) (z:Site n) : splitter (n:=n) dvd_rfl z=z := by
  obtain ⟨a, rfl⟩ : ∃a:Cover,z=wrap n a := ⟨_,(wrap_lift _).symm⟩
  rw [branch]

theorem atSite (n:Side) (z:Site n) (u:Fin (Pages n n)) :
    (page dvd_rfl z u).val=z := by
  have hi:= (page (N:=n) dvd_rfl z u).property
  exact (identity n _).symm.trans ((Shingle.posted _ _ _).mp hi)

variable {G:Gauge}{n:Side}{V I X:Type}[DecidableEq V]
    {P:Passport n V}{R:Census V}(M:I→Row P R G X)(w:V→ℕ)(t:X)
    {σ:ℝ}{order:ℕ}(paid:Air.Staff M (fun i=>(M i).paint t) w σ order)
    (L:Layout G)(tape:Finset Age)

 include paid in
theorem original (j:ℕ)(A:Stationary.Link G n) :
    peek (f:=n) dvd_rfl M w L tape t j A =
      Air.discharge (Air.craft M (fun i=>(M i).paint t) w L tape) j (Stationary.arm G n 1 A) := by
  classical
  letI : Fintype V := Fintype.ofInjective R.fire (fun a b h => (R.fire_inj a b).mp h)
  have count: Pages n n=1:=by simp [Pages,Nat.div_self n.pos]
  let home:Fin (Pages n n):=⟨0,by omega⟩
  have unique (u:Fin (Pages n n)):u=home:=by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (by have:=u.isLt;change u.val≤0;omega)
  rw [peek_pages dvd_rfl M w L tape t A j paid, Finset.sum_eq_single home]
  · have paper:=reads_page (f:=n) dvd_rfl M w L tape t A j paid home
    have issued:=Air.compared M (fun i=>(M i).paint t) w paid L tape A j
    apply paper.unique
    convert issued using 1
    funext i
    unfold reading Row.markReceipt
    rw [recenter,atSite]
    rfl
  · intro b _ hb
    exact (hb (unique b)).elim
  · simp

end YM.Integration.WilsonMeasuredOriginalPeriodRead
end
