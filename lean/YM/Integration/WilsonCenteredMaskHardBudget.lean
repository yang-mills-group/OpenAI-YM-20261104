import YM.Integration.WilsonCenteredOccupiedFamilies
import YM.Integration.WilsonCenteredHardWallet

/-! The whole retained polynomial of an occupied hard owner is charged at
one of the actual source locations in the captured mask. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMaskHardBudget
open Finset Marker Wilson RG Lattice Push.Local QuadraticLocal WilsonCenteredOccupiedFamilies
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R) (w : V→ℝ) (hw : ∀v,0<w v)

include hw
theorem original (s : R.Mode) {α κ : ℝ} (paid : H.Paid w P.p.B α κ) :
    ∃ e : ℕ→ℝ, (∀j,0≤e j) ∧ (∀j,e j≠0 → ∃v∈s.val,o v∈Push.Local.patch P.activities j) ∧
    (∀j x U,Poly.price w (dye s (H.hard x j U))≤e j) ∧
    SumBudget (fun j=>Real.exp (α*coverNumber P.p.B (Push.Local.patch P.activities j))*e j) (s.val.card*κ) :=by
  obtain ⟨g,cap,spent⟩:=paid.wages
  let atName v j:=if o v∈Push.Local.patch P.activities j then Poly.price w (g j) else 0
  let e j:=∑v∈s.val,atName v j
  let span j:=Real.exp (α*coverNumber P.p.B (Push.Local.patch P.activities j))
  have nn v j : 0≤atName v j := by
    dsimp only [atName];split
    · exact Poly.nonnegative hw _
    · exact le_rfl
  have empty (j) (off : ¬∃v∈s.val,o v∈Push.Local.patch P.activities j) (x U) : dye s (H.hard x j U)=0 := by
    ext t
    change (dye s (H.hard x j U)).part t=0
    by_cases idle : t=R.quiet
    · subst t;exact quiet s _
    rw [marked s t _ idle]
    split
    next inside =>
      by_contra live
      have used : t.val.Nonempty :=by
        by_contra hn
        exact idle (Subtype.ext (not_nonempty_iff_eq_empty.mp hn))
      obtain ⟨v,hv⟩:=used
      exact off ⟨v,inside hv,(H.locality x j).carry U t live v hv⟩
    rfl
  have tariff v : SumBudget (fun j=>span j*atName v j) κ :=by
    convert spent (o v) using 1
    ext j
    by_cases yes : o v∈Push.Local.patch P.activities j <;> simp [atName,span,yes,Push.Local.patch,mul_comm] at *
  refine ⟨e,fun j=>sum_nonneg (fun v _=>nn v j),?_,?_,?_⟩
  · intro j nonzero
    by_contra void
    apply nonzero
    apply sum_eq_zero
    intro v hv
    exact if_neg (fun h=>void ⟨v,hv,h⟩)
  · intro j x U
    by_cases active : ∃v∈s.val,o v∈Push.Local.patch P.activities j
    · obtain ⟨v,member,hit⟩:=active
      have paid:=single_le_sum (fun i _=>nn i j) member
      have bid : Poly.price w (g j)≤e j := by simpa only [atName,if_pos hit] using paid
      exact ((absolute s _ w hw).trans ((cap j x U).reprice w hw)).trans bid
    have zero : Poly.price w (0:Poly R)=0 := by simp [Poly.price]
    rw [empty j active,zero]
    exact sum_nonneg (fun v _=>nn v j)
  · have sums (S : Finset V) : SumBudget (fun j=>span j*∑v∈S,atName v j) (S.card*κ) :=by
      induction S using Finset.induction_on with
      | empty => simp [SumBudget]
      | @insert v S off ih =>
        have total:=sumBudget_add (tariff v) ih
        convert total using 1
        · funext j;rw [sum_insert off,mul_add]
        · rw [card_insert_of_notMem off,Nat.cast_succ,add_mul,one_mul,add_comm]
    exact sums s.val

end YM.Integration.WilsonCenteredMaskHardBudget
