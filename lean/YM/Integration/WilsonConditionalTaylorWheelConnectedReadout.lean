import YM.Integration.WilsonConditionalTaylorWheelMaskReading
import YM.FormalBulk08.Mesa.Rift

/-! Connected logarithm for the true distinct labeled marks, after the same
external marked tests have been applied to every subset. This preserves the
vacuum contraction between the two marks in particular. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelConnectedReadout
open Function Filter Lattice Laurent RG Wilson Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Mesa
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}

def read (A:Case D) (S:Finset I):Era G (Pen D S)→ₗ[ℝ]Mesa.Pot G where
  toFun X:=pPly A S X.2
  map_add' _x _y:=(pPly A S).map_add _ _
  map_smul' _c _x:=(pPly A S).map_smul _ _

def logged {U:Type} (M:Finset I→Pal ℝ U) (S:Finset I):Pal ℝ U:=
  if _h:S=∅ then 0 else M S-(S.card:ℝ)⁻¹ • ∑ J∈S.powerset,
    if _w:J⊆S∧J≠S then (J.card:ℝ) • Mer.woad (logged M J) (M (S\J)) else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (lt_of_le_of_ne _w.1 _w.2)

def finiteRead (A:Case D) (S:Finset I) (n:Side):Era G (Pen D S)→ₗ[ℝ]PChart G n where
  toFun X:=pPly A S (X.1 n)
  map_add' _x _y:=(pPly A S).map_add _ _
  map_smul' _c _x:=(pPly A S).map_smul _ _

private theorem readLog {U:Type} (row:∀S:Finset I,Era G (Pen D S)→ₗ[ℝ]Pal ℝ U)
    (join:∀ (S J:Finset I)(sub:J⊆S)(P:Era G (Pen D J))(Q:Era G (Pen D (S\J))),
      row S (waxV sub P Q)=Mer.woad (row J P) (row (S\J) Q))
    (M:family G D)(S:Finset I):row S (reverseO M S)=logged (fun J=>row J (M J)) S:=by
  induction S using Finset.strongInductionOn
  case _ S ih=>
    by_cases h:S=∅
    · subst S
      rw [empty_reverse,map_zero,logged,dif_pos rfl]
    · rw [reverseO,dif_neg h,logged,dif_neg h,map_sub,map_smul,map_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro J _
      by_cases w:J⊆S∧J≠S
      · rw [dif_pos w,dif_pos w,map_smul]
        congr 1
        exact (join S J w.1 (reverseO M J) (M (S\J))).trans (congrArg (fun t=>Mer.woad t (row (S\J) (M (S\J)))) (ih J (lt_of_le_of_ne w.1 w.2)))
      · rw [dif_neg w,dif_neg w,map_zero]

theorem tested (M:family G D) (A:Case D) (S:Finset I):
    read A S (reverseO M S)=logged (fun J=>read A J (M J)) S:=
  readLog (read A) (fun _ _ sub P Q=>fp sub P.2 Q.2 A) M S

theorem testedFinite (M:family G D) (A:Case D) (S:Finset I) (n:Side):
    finiteRead A S n (reverseO M S)=logged (fun J=>finiteRead A J n (M J)) S:=
  readLog (fun J=>finiteRead A J n) (fun _ _ sub P Q=>fp sub (P.1 n) (Q.1 n) A) M S

theorem original (K:family G D) (k:I→ℕ) (well:Eu k K) (quiet:K ∅=0) (A:Case D) (S:Finset I):
    read A S (K S)=logged (fun J=>read A J (levelsO K J)) S:=by
  have eqn:=tested (levelsO K) A S
  rw [rectify K well quiet] at eqn
  exact eqn
theorem finite (K:family G D) (k:I→ℕ) (well:Eu k K) (quiet:K ∅=0) (A:Case D) (S:Finset I) (n:Side):
    finiteRead A S n (K S)=logged (fun J=>finiteRead A J n (levelsO K J)) S:=by
  have eqn:=testedFinite (levelsO K) A S n
  rw [rectify K well quiet] at eqn
  exact eqn

end YM.Integration.WilsonConditionalTaylorWheelConnectedReadout
end

