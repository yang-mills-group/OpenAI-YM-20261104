import YM.RG01Estimate.BrimPress
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Oriole

/-!
# Collect the pre-reset log split

Use Perspective projection and glyph estimates with the *actual* analytic log
lens. Unmarked alphabet aligned, keep the omitted germs. Desk with common anchor
and same-E identifying permutation. Transfer identities can use Account from the
prior Estimate modules. No comparison of representations without their own budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Acquire

open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Meadow
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ s a α : ℝ} {i j k m n : ℕ} {χ : Chi}
    {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R}

-- early budget converters
lemma branch_budget {ι : Type} {p : BudgetPoint} {A : ι→RegularAddress c}
    (Z : ι → Prop) {F F' : ι → Config G c→ℝ} {a u : ℝ} (h : Budget p A F a) (hp : Budget p A F' u) :
    Budget p A (fun i=> if Z i then F i else F' i) (a+u) := by
  obtain ⟨k,hT,hK⟩:=h; obtain ⟨l,hS,hL⟩:=hp
  refine ⟨fun i=> if Z i then k i else l i,fun i=>?_,fun i=>?_⟩
  swap
  · dsimp only; split
    next => exact hK _
    next => exact hL _
  have he := budget_plus (hT i) (hS i)
  refine budget_mono he (fun j=>?_) fun j=> ?_
  · dsimp only; split
    next => split
            exact mul_nonneg (hK _).2.1 (Real.exp_nonneg _)
            exact mul_nonneg (hL _).2.1 (Real.exp_nonneg _)
    exact le_rfl
  dsimp only; split
  next => split
          exact le_add_of_nonneg_right (mul_nonneg (hL _).2.1 (Real.exp_nonneg _))
          exact le_add_of_nonneg_left (mul_nonneg (hK _).2.1 (Real.exp_nonneg _))
  linarith only
lemma budget_zeros {ι : Type} (A : ι→RegularAddress c) (p : BudgetPoint) :
    Budget p A (fun _=> (0:Config G c→ℝ)) 0 := by
  refine ⟨fun _=>0,fun i=> by simp [SumBudget],fun i=> ?_⟩
  refine ⟨CouplingShape.reg_const _,?_⟩
  simpa only [abs_zero] using!
    (CouplingShape.sup_const (G:=G) (p:=p) (o:=(A i).site) (X:=(A i).support) 0)
lemma budget_cut {ι : Type} {p : BudgetPoint} {A : ι→RegularAddress c}
    (Z : ι → Prop) {F : ι → Config G c→ℝ} {a : ℝ} (h : Budget p A F a) :
    Budget p A (fun i=> if Z i then F i else 0) a := by
  have ht:= branch_budget Z h (budget_zeros A p (G:=G)); rwa [add_zero] at ht
lemma budget_concat {ι τ : Type} {A : ι→ RegularAddress c} {M : τ → RegularAddress c} {p : BudgetPoint}
    {F : ι → Config G c→ℝ} {F' : τ → Config G c→ℝ} {a u : ℝ} (h : Budget p A F a) (hp : Budget p M F' u) :
    Budget p (Sum.elim A M) (Sum.elim F F') (a+u) := by
  obtain ⟨k,hT,hK⟩:=h; obtain ⟨l,hS,hL⟩:=hp
  exact ⟨Sum.elim k l, fun i=> Cost.sum (hT i) (hS i),fun i=> by rcases i with i|i; exact hK _; exact hL _⟩

variable (H : Cash W s μ L Q o α T R) (χ : Chi) (M : Alliance H H 1 0)
  {η θ T' : ℝ} (hM : M.units=Equiv.refl _) {p : BudgetPoint} (ht : p.threshold=Pressure.temp s)
  (hB : p.B=radiusB s) (hi : preExponent p ≤ η) {x : ℝ} {Y D d A u v B q w i' : ℝ}
  (N : Captain H j Y D d A u v B q w k χ)
include ht
lemma from_hit (Z : H.fragrances → Prop) (hg : p.order ≤ j) (hr : p.power ≤ m) (hB : p.B=radiusB s)
    (hi : preExponent p ≤ η)
    (h : Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun t=> if Z t then N.markΦ t m else 0) η x) :
    Budget p (dashboard H) (fun z=> if Z (M.furrow z) then Song.sequence H M χ z else 0) x := by
  have he := VacuumListing.dash_hit H p M hB hi _ h
  refine ⟨_,he,fun z=>?_⟩
  dsimp only [comp_apply]; split; exact VacuumListing.pocket_dash H p χ M N ht hg hr z
  next => refine ⟨CouplingShape.reg_const _,?_⟩
          simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(dashboard H z).site) (X:=(dashboard H z).support) 0)

variable (E : Set ℕ) (r : ℕ)
namespace Groups
open Fate
variable {H χ}
def isolation (H : Cash W s μ L Q o α T R) (z : H.fragrances) : Prop := inherits E z ∧ ¬high z r
def bad_renewal (z : H.fragrances) := ¬ (isolation E r H z ∨ showcase E r z)
omit ht
include hM
lemma lift_icon (i : ℕ) : M.furrow (icon H i) = icon H i := Beam.mimics H M hM _
lemma elevated (z : H.fragrances) : (∃ i∈E,M.furrow z=icon H i) ↔ ∃ i∈E,z=icon H i := by
  apply exists_congr; intro i
  refine and_congr_right fun _=> ?_
  exact ⟨fun he=> M.furrow.injective (he.trans (lift_icon M hM i).symm),fun he=> he.symm ▸ lift_icon M hM i⟩
end Groups

include hi hB hM
include N in
lemma inherit_budget (hg : p.order ≤ j) (hr : p.power ≤ m) (hx : Single.Pays H p E χ η θ) :
    Budget p (dashboard H) (fun z=> if Groups.isolation E r H (M.furrow z) then Song.sequence H M χ z else 0) θ := by
  obtain ⟨f,hP,hF⟩:= hx.envelope
  let e' : ℕ ↪ H.fragrances:= ⟨icon H,icon_inj H⟩; let f' (i:H.fragrances):= Function.extend e' f 0 i
  let A i:= if Groups.isolation E r H (M.furrow i) then f' i else 0
  have hu (z): p.Regular (dashboard H z).support (if Groups.isolation E r H (M.furrow z) then Song.sequence H M χ z else 0) ∧ p.supBounds (dashboard H z).site (dashboard H z).support (if Groups.isolation E r H (M.furrow z) then Song.sequence H M χ z else 0) (A z) := by
    unfold A; split
    next hp=>
      obtain ⟨i,hi,rfl⟩:= (Groups.elevated M hM E z).1 hp.1
      rw [show f' (icon H i)=_ from e'.injective.extend_apply _ _ i]
      refine ⟨(VacuumListing.pocket_dash H p χ M N ht hg hr _).1,?_⟩
      have hy:= hF i hi (hB.symm ▸ (Fate.cover_inherited H i (by
        rw [← Groups.lift_icon M hM i]; exact hp.2)))
      rw [Song.sequence, Groups.lift_icon M hM i,impact]; simpa only [abs_neg,abs_one,one_mul] using (CouplingShape.sup_scale (-1) hy)
    next => refine ⟨CouplingShape.reg_const _,?_⟩
            simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(dashboard H z).site) (X:=(dashboard H z).support) 0)
  refine ⟨A,fun i=>?_,hu⟩; apply Beam.wallet e' ?_ ?_
  · refine budget_mono (hP i) (fun i'=> ?_) fun i'=> ?_
    · dsimp only; split; next => exact mul_nonneg (hu _).2.1 (Real.exp_nonneg _)
      exact le_rfl
    by_cases h: Groups.isolation E r H (M.furrow (e' i'))
    · dsimp only; simp only [show dashboard H (e' i')=plate H i' from impact H i']; split
      next =>
        have ha : A (e' i')=f i':= (if_pos h : A (e' i')=_).trans (e'.injective.extend_apply _ _ _)
        apply le_trans (b:=A (e' i')*Real.exp (η*coverNumber p.B (plate H i').support)) ?_
        · rw [ha]
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))) (hu _).2.1
      next => exact le_rfl
    unfold A; rw [if_neg h, zero_mul,ite_self]; exact (hP i).1 _
  intro b hb
  have hh : ¬Groups.isolation E r H (M.furrow b):= fun he=> hb (let ⟨j,_,hF⟩:= (Groups.elevated M hM E b).1 he.1; ⟨j,hF.symm⟩)
  unfold A; rw [if_neg hh, zero_mul, ite_self]

section tails
omit hM
open Groups Fate
lemma remainder (hd : Admission Q L W μ η o j m r χ s)
    (hg : p.order ≤ j) (hp : p.power ≤ m) (hx: Inherit.Debits R E (Fate.debt r G L s)) (hT : Stamp T) :
    Budget p (dashboard H) (fun z=> if bad_renewal (H:=H) E (Fate.steps r) (M.furrow z) then Song.sequence H M χ z else 0)
      (Fate.target r G L s + Fate.target r G L s) := by
  let p' := Fate.steps r
  obtain ⟨ht',hA⟩:= hd; let X:= Fate.target r G L s; let D:= Height.grow G L s
  let u:=Fate.wE Q L r s; let v:=Fate.wK Q L r s; let Z (x):= clusterCost (H:=H) (Reprice.weigh c f E u v) D x
  obtain ⟨Y₁,Y₂⟩:= hA c f S T hT R α H
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,N,hP',hTy⟩:= Y₁
  let U₀ x:=high (H:=H) x p'
  have he:= from_hit H χ M ht N U₀ hg hp hB hi hP'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,N',hU,hD,hN⟩:= Y₂ E hx
  let U₁ x := D^2 * u ≤ Z x
  have ht:= from_hit H χ M ‹p.threshold=_› N' U₁ hg hp hB hi hN
  let G₀ x:= M.furrow x
  refine Eq.mp ?_ (budget_cut (p:=p) (fun z=> bad_renewal (H:=H) E p' (M.furrow z)) (branch_budget (fun x=> high (M.furrow x) p') he ht))
  congr 1
  funext z
  split
  next h =>
    split
    next hh=> rfl
    next hh=>
      split
      · rfl
      next hK=>
        symm; funext V
        by_contra h'
        change -1* March.stream H χ V (M.furrow z)≠ 0 at h'; apply hK
        obtain ⟨hb,ht⟩:= not_or.mp h
        exact Fate.covered E (M.furrow z) V (right_ne_zero_of_mul h') p' (by unfold p' Fate.steps; omega)
          hh (fun k=> hb ⟨k,hh⟩) ht hU (one_le_mul_of_one_le_of_one_le hD hU) hD (show D*u≤v from le_rfl)
  next => rfl
end tails
end YM.RG01Estimate.Acquire
