import YM.Integration.WilsonOriginalAlternativeNames
import YM.Marker.Weight

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativePurse
open Finset Function Marker RG05Readout.Many WilsonOriginalAlternativeNames
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V] (R:Census V)

def copiesBound : ℝ := Fintype.card (board R).Mode

theorem bound_one : 1≤copiesBound R := by
  haveI : Nonempty (board R).Mode := ⟨(board R).quiet⟩
  change (1:ℝ) ≤ (Fintype.card (board R).Mode:ℝ)
  exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (board R).Mode)))

def wallet (w:V→ℝ) (j:V×Port) : ℝ := w j.1/copiesBound R

theorem positive {w:V→ℝ} (wp:∀i,0<w i) (j:V×Port) : 0<wallet R w j :=
  div_pos (wp j.1) (lt_of_lt_of_le zero_lt_one (bound_one R))

theorem quiet (a:Poly R) : (inheritAll R a).part (board R).quiet=a.part R.quiet := by
  rw [inherited];simp [Census.quiet,base,Lit.climb]

theorem active (s:(board R).Mode) :
    (∏j∈s.val,retain j.2)=if ∀j∈s.val,j.2≠1 then 1 else 0 := by
  classical
  split
  next h=> exact Finset.prod_eq_one fun j hj=>if_neg (h j hj)
  next h=>
    push Not at h
    obtain ⟨j,hj,e⟩:=h
    exact Finset.prod_eq_zero hj (by simp [retain,e])

theorem part (a:Poly R) (s:(board R).Mode) :
    (inheritAll R a).part s = if ∀j∈s.val,j.2≠1 then a.part (base R s) else 0 := by
  rw [inherited,active];split <;> simp

theorem scaled (w:V→ℝ) (s:(board R).Mode) :
    Poly.toll (wallet R w) s=Poly.toll w (base R s)/(copiesBound R)^s.val.card := by
  unfold wallet Poly.toll base Lit.climb
  rw [Finset.prod_image (legal R s).2, Finset.prod_div_distrib]
  simp

theorem hot (s:(board R).Mode) (h:base R s≠R.quiet) : 1 ≤ (s.val).card := by
  by_contra! he
  have empty:s.val=∅:=Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos (by omega))
  apply h
  apply Subtype.ext
  change s.val.image Prod.fst=∅
  rw [empty,Finset.image_empty]

theorem row {w:V→ℝ} (wp:∀i,0<w i) (s:(board R).Mode) (h:base R s≠R.quiet) :
    Poly.toll (wallet R w) s ≤ Poly.toll w (base R s)/copiesBound R := by
  rw [scaled]
  apply div_le_div_of_nonneg_left (Poly.worth wp _).le (lt_of_lt_of_le zero_lt_one (bound_one R))
  simpa using pow_le_pow_right₀ (bound_one R) (hot R s h)

theorem priced {w:V→ℝ} (wp:∀i,0<w i) (s:R.Mode) (c:ℂ) :
    Poly.price (wallet R w) (inheritAll R (Poly.send s c)) ≤ Poly.toll w s*‖c‖ := by
  by_cases h:s=R.quiet
  · subst s
    have q:inheritAll R (Poly.send R.quiet c)=Poly.send (board R).quiet c:=(inheritAll R).commutes c
    simp [q]
  let b:=Poly.toll w s*‖c‖
  have bp:0≤b:=mul_nonneg (Poly.worth wp s).le (norm_nonneg _)
  calc
    _ ≤ ∑ _: (board R).Mode,b/copiesBound R := by
      apply Finset.sum_le_sum
      intro t _
      rw [part]
      by_cases ht:base R t=s
      · have pw:=row R wp t (fun eq=>h (ht.symm.trans eq))
        rw [ht] at pw ⊢
        split
        · rw [Poly.part_send,if_pos rfl]
          change _≤Poly.toll w s*‖c‖/_
          simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right pw (norm_nonneg c)
        · simpa using (div_nonneg bp (bound_one R |>.trans' zero_le_one))
      · simp [Poly.part_send,ht,div_nonneg bp (bound_one R |>.trans' zero_le_one)]
    _ = b := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
      change copiesBound R*(b/copiesBound R)=b
      field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one (bound_one R))]

theorem total {w:V→ℝ} (wp:∀i,0<w i) (a:Poly R) :
    Poly.price (wallet R w) (inheritAll R a)≤Poly.price w a := by
  conv_lhs => rw [← Poly.studs a,map_sum]
  exact (Poly.batch (positive R wp) ..).trans (Finset.sum_le_sum fun s _=>priced R wp s _)

end YM.Integration.WilsonOriginalAlternativePurse
