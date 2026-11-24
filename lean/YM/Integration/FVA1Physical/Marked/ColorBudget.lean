import YM.Integration.FVA1Physical.Marked.ColorRows
import YM.Integration.FVA1Physical.Marked.M7a

/-! The full represented norm of the complex, row-polarized remainder.
The same support, factorial norm, cutoff and divided forced budget serve
every coefficient. The only price is half the already purchased radii. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter MeasureTheory Lattice RG Wilson Marker LocalComparison RG3.Script.Picnic Push.AbsoluteSums
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge} {n : Side} {P : Rep G n}
    {o : I→Site n} {T : Taste (Finset I) o P B} {p : BudgetPoint} {w : I→ℝ} {κ a b : ℝ}

omit [DecidableEq I] in
private theorem blend_ne_zero {E : Type*} [AddCommMonoid E] [Module ℂ E] (s : Finset I)
    (F : Finset I→E) (h : blend s F ≠ 0) : ∃ t∈s.powerset,F t≠0 := by
  by_contra! h₀
  apply h
  exact Finset.sum_eq_zero fun t ht=>by rw [h₀ t ht,smul_zero]

theorem colorTaste_active (H : ∀ t,(T.leaf t).Active) (u : Unit) : ((colorTaste T).leaf u).Active := by
  let Z := (H ∅).articles
  refine ⟨⟨Z.proper,Z.pins,?_,Z.occurs,?_,?_,?_,?_,?_⟩,⟨(H ∅).captions.card,(H ∅).captions.pins⟩⟩
  · exact fun i=>regular_blend (T.menu.rays i).val _ (fun t _=>(H t).articles.regular i)
  · intro i j h
    obtain ⟨t,_,ht⟩ := blend_ne_zero (T.menu.marks i j).val (fun t=>T.menu.force t i j) h
    exact (H t).articles.retained i j ht
  · intro i j U V agree mask
    change blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) U=blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) V
    rw [blend_eval,blend_eval]
    apply congrArg
    exact funext fun t=>(H t).articles.inspects i j U V agree mask
  · intro i j v hv
    change blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) v ≠ 0 at hv
    rw [blend_eval] at hv
    obtain ⟨t,_,ht⟩ := blend_ne_zero (T.menu.marks i j).val (fun t=>T.menu.force t i j v) hv
    exact (H t).articles.keeps i j v ht
  · intro i j
    change Measurable (blend _ (fun t=>T.menu.force t i j))
    rw [show blend (T.menu.marks i j).val (fun t=>T.menu.force t i j)=fun v=>blend (T.menu.marks i j).val (fun t=>T.menu.force t i j v) from funext (blend_eval _ _)]
    exact Finset.measurable_fun_sum _ fun t _=>(H t).articles.meas i j |>.const_smul (Complex.I^t.card)
  intro i j u v
  change blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) _ = blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) _
  rw [blend_eval,blend_eval]
  apply congrArg
  exact funext fun t=>(H t).articles.invi i j u v

private theorem half_mass (w : I→ℝ) (s : B.Mode) (p : BudgetPoint) (S : Support n) (a : ℝ) :
    Poly.toll (fun j=>w j/2) s * p.mass S (copies s.val*a) = Poly.toll w s*p.mass S a := by
  unfold BudgetPoint.mass
  rw [←half_toll w s]
  ring

def colored_budget (H : FullBudget p T w κ a b) : FullBudget p (colorTaste T) (fun j=>w j/2) κ a b where
  white := fun i=>copies (T.menu.rays i).val*H.white i
  black := fun i=>copies (T.menu.marks i.1 i.2).val*H.black i
  gold := fun i=>copies (T.tag i).val*H.gold i
  unitBound := fun j=>2*H.unitBound j
  active := colorTaste_active H.active
  radii := fun j=>half_pos (H.radii j)
  divisor := H.divisor
  white_nonnegative := fun i=>mul_nonneg (Nat.cast_nonneg _) (H.white_nonnegative i)
  regular := fun i=>⟨fun _ j hj=>blend_grain (T.menu.rays i).val _ _ _ (fun t=>H.regular_law t i)
    (fun t=>(H.regular i).controls t j hj)⟩
  regular_law := fun _ i=>regular_blend (T.menu.rays i).val _ (fun t _=>H.regular_law t i)
  black_nonnegative := fun i=>mul_nonneg (Nat.cast_nonneg _) (H.black_nonnegative i)
  forced := by
    intro _ i j v
    change ‖blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) v‖ ≤ _
    rw [blend_eval]
    exact norm_blend _ _ (fun t _=>H.forced t i j v)
  gold_nonnegative := fun i=>mul_nonneg (Nat.cast_nonneg _) (H.gold_nonnegative i)
  caption := fun _ i=>norm_blend _ _ (fun t _=> H.caption t i)
  unit_nonnegative := fun i=>mul_nonneg zero_le_two (H.unit_nonnegative i)
  unit := by
    intro _ v
    have h := norm_blend ({v} : Finset I) (fun t=>T.menu.global t v) (fun t _=>H.unit t v)
    change ‖blend ({v} : Finset I) (fun t=>T.menu.global t v)‖ ≤ _
    simpa only [copies,Finset.card_powerset,Finset.card_singleton,pow_one,Nat.cast_ofNat] using h
  regularTotal := by
    intro v
    obtain ⟨R,S,regular,cap,both⟩ := H.regularTotal v
    refine ⟨R,S,?_,?_,?_⟩
    · change SumBudget (fun i=>if v∈(T.menu.rays i).val then _ else 0) R
      simpa only [colorTaste,half_mass] using regular
    · change SumBudget (fun i=>if v∈(T.tag i).val then _ else 0) S
      simpa only [colorTaste,half_mass] using cap
    linarith only [both]
  forcedTotal := by
    intro v
    change SumBudget (fun i : ℕ×ℕ=>if v∈(T.menu.marks i.1 i.2).val then _ else 0) _
    simpa only [colorTaste,half_mass] using H.forcedTotal v

end YM.Integration.FVA1Physical.Marked
