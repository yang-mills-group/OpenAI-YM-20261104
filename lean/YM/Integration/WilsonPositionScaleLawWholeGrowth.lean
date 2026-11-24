import YM.Integration.WilsonPositionScaleLawContract

/-! A polynomial upper-column bound at a pre-elected original anchor feeds the
strict lower-block contraction without losing a power at each successive step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawWholeGrowth
open Function Filter Set Finset Spec Table Extraction OPE Climb PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawGrade (grade half)
open WilsonPositionScaleLawFixed (top normalized)
open WilsonPositionScaleLawWhole (full low)
open WilsonPositionScaleLawClock (radius)
open scoped Topology Classical BigOperators

def weight (p n:ℕ):ℝ:=((n:ℝ)+1)^p

theorem increasing (p:ℕ):Monotone (weight p):=by
  intro n m h
  change ((n:ℝ)+1)^p≤((m:ℝ)+1)^p
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1) p

theorem positive (p n:ℕ):1≤weight p n:=by
  change 1≤((n:ℝ)+1)^p
  exact one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n])

theorem damp (K p:ℕ)(L H:ℕ→ℝ)(B:ℝ)(l0:0≤L K)(b0:0≤B)
    (head:∀n,K≤n→H n≤weight p n*B)(link:∀n,K≤n→3*L (n+1)≤2*L n+H (n+1)):
    ∀n,K≤n→L n≤weight p n*(L K+B):=by
  intro n hn
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero=>
    simp only [Nat.add_zero]
    exact (le_add_of_nonneg_right b0).trans (le_mul_of_one_le_left (add_nonneg l0 b0) (positive p K))
  | succ k ih=>
    have old:=ih.trans (mul_le_mul_of_nonneg_right (increasing p (Nat.le_succ (K+k))) (add_nonneg l0 b0))
    have hpos:0≤weight p (K+k+1):=zero_le_one.trans (positive ..)
    have current: H (K+k+1)≤weight p (K+k+1)*(L K+B):=(head _ (by omega)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left l0) hpos)
    have eq:=link (K+k) (by omega)
    change L (K+k+1)≤weight p (K+k+1)*(L K+B)
    linarith

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)

theorem cap {d:ℕ}(r:ℝ)(n:ℕ)(O:S.Field d):
    grade R.family (top d) (full F J Z d (radius r n) O)=normalized F J Z d r n O:=by
  rw [WilsonPositionScaleLawWhole.full,map_smul];rfl

theorem next (r:ℝ)(n:ℕ):half.val*radius r n=radius r (n+1):=by dsimp [half,radius];ring

theorem lowPositive {d:ℕ}(v:(Bel R.family.book).Field d):0≤low R.family v:=Finset.sum_nonneg fun _ _=>norm_nonneg _

end YM.Integration.WilsonPositionScaleLawWholeGrowth
end
