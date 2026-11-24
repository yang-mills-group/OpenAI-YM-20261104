import YM.Integration.WilsonPositionProgramTrialCellDigits
import YM.Integration.WilsonReceivedFixedDigitHistory

/-! The retained finite-child itinerary uses the true digit of each separate
source between its filing and its first stop. The extra older stop fixes all
these digits under a common displacement by an entire older block. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFixedDigits
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonReceivedFixedDigitHistory
open WilsonPositionProgramTrialCellDigits
open scoped Classical
variable {G : Gauge} {I : Type}

def parents (S : Schedule) {j K : ℕ} (upper : j ≤ K) (o : I → Cover) : I → Cover :=
  fun i => parentC (S.toDepth upper 0).count (o i)

def cells (L : Levels G) (c K : ℕ) (o : I → Cover) : Digits L I :=
  fun j i => if h : c ≤ j ∧ j < K then wrap (L.S.block j) (parents L.S h.2 (o) i) else 0

theorem original (L : Levels G) {w c K : ℕ} (early : w ≤ c) (filed : c ≤ K)
    (o : I → Cover) (anchor : I) :
    cells L c K (residual L.S (early.trans filed) o anchor)=cells L c K o := by
  funext j i
  dsimp only [cells]
  split_ifs with h
  · have lower := early.trans h.1
    have specific : j+1 ≤ K := h.2
    have move := (WilsonPositionProgramTrialCellDigits.original L.S
      (lower.trans (Nat.le_succ _)) specific o anchor i).1
    change wrap (L.S.block j) (parentC _ (residual _ _ _ _ _))=_
    rw [move]
    have factor : (L.S.toDepth (lower.trans (Nat.le_succ j)) 0).count.val=
        (L.S.block j).val*(L.S.toDepth lower 0).count.val :=
      Next.Rank.Station.size_comp (L.S.toDepth lower 0) (L.S.oneStep j 0) _
    rw [factor,mul_smul,sub_eq_add_neg,←smul_neg]
    exact (slide _ _ _).2
  · rfl

theorem at_stop (L : Levels G) {w c K : ℕ} (early : w ≤ c) (filed : c ≤ K)
    (o : I → Cover) (anchor : I) :
    parents L.S filed (residual L.S (early.trans filed) o anchor)=
      fun i => (L.S.toDepth early 0).count.val • (-ancestor L.S (early.trans filed) o anchor)+
        parents L.S filed o i := by
  funext i
  rw [smul_neg,add_comm]
  exact (WilsonPositionProgramTrialCellDigits.original L.S early filed o anchor i).1

end YM.Integration.WilsonPositionProgramTrialFixedDigits
