import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskSeries
import YM.Integration.WilsonVacuumPreResetModelBoard
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGram

/-! The genuine two ordered walks and the independent low packet's declared
halo both enter the physical exceptional event at an occupied site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open IterationFour IterationFour.Vacuum Next.Scheduling Function Filter Finset Lattice RG Wilson Precision Stationary
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open Comparison.Density.Render PhysicalNext.Repeat PhysicalNext.Repeat.Legato MeasureTheory OPE.Therm
open scoped Classical BigOperators
open private pairIndices from YM.Integration.WilsonPhysicalHistoryRetainedSpringGram
variable {G : Gauge} {n : Side}

def gramLow (i : ℕ) : Low:=((pairIndices i).1,Sum.inr (pairIndices i).2)

theorem gram_home (K : PathData G) (p : BudgetPoint) (o : Site n) (i : ℕ) :
    ((gramLow i).home K p o).card ≤ ((gramEntries K i).footprint o).card+(2*p.B+1)^4 := by
  let g:=gramEntries K i
  let l:=Wages.walkCuts ((K.row (pairIndices i).1 (pairIndices i).2.1).2) o
  let r:=Wages.walkCuts ((K.row (pairIndices i).1 (pairIndices i).2.2).2) o
  have left : l⊆g.footprint o := stows o g (j:=0)
  have right : r⊆g.footprint o := stows o g (j:=1)
  have subset : (gramLow i).home K p o ⊆ g.footprint o ∪ halo p.B {o} := by
    change (halo p.B {o} ∪ l) ∪ r⊆_
    exact union_subset (union_subset subset_union_right (left.trans subset_union_left)) (right.trans subset_union_left)
  have halo := Corona.halo_size ({o}:Support n) p.B
  simpa only [card_singleton,one_mul,two_mul] using
    (card_le_card subset).trans ((card_union_le ..).trans (Nat.add_le_add_left halo (g.footprint o).card))

theorem gram_plain (K : PathData G) (c : Clip) (x : Site n) (U : Config G n) (i : ℕ) :
    (gramLow i).mark K c*(gramLow i).plain K x U=(gramEntries K i).unmasked U x := by
  change _=aTerm (gramPath K (pairIndices i)) (expandAt x U)
  rw [gram_eval]
  simp only [gramLow,Low.mark,Low.plain,Sum.elim_inr,Low.left,Low.right,PathData.ellTerms,
    real_inner_smul_left,real_inner_smul_right]
  ring

def maskedGram (K : PathData G) (c : Clip) (p : BudgetPoint) (v : Seat n) (U : Config G n) : ℝ:=
  ∑'i,(gramLow i).maskedPlain K c 0 p (v.view U)

theorem spring_mask_gram (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per (K : PathData G) (c : Clip) (σ D Λ : ℝ),0<σ→
      K.Bounds c σ D Λ→∀ (p : BudgetPoint),p.threshold=(R.family.path.rep N per j).p.threshold→
      ∀ (v : Seat (R.family.side j per)),
      let C:=gramCost G D
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedGram K c p v U-
        ∑'i,(gramEntries K i).unmasked (v.view U) 0
      Measurable f ∧ (∀U,‖f U‖≤C*4) ∧
        (∫U,‖f U‖ ∂scene R.family.path N per j)≤C*(4*(5+((2*p.B+1)^4:ℕ)+σ⁻¹)*fee) := by
  filter_upwards [spring_mask_series R simple heat q] with j paid N hj per K c σ D Λ hs path p hp v C fee f
  let A:=gramEntries K
  let n:=R.family.side j per
  let X:=fun i=>(gramLow i).home K p (0:Site n)
  let Gf:=fun i (U : Config G n)=>(A i).unmasked U 0
  have cap (i U) : ‖Gf i U‖≤(A i).magnitude*2^(2:ℕ)*1 := by
    simpa only [Gf,Real.norm_eq_abs,mul_one] using (A i).unmasked_bound U (0:Site n)
  have tst:=paid N hj per 2 A σ C 1 hs zero_le_one (gram_finance K path) v.1 v.2 (0:Site n)
    X ((2*p.B+1)^4) Gf (gram_home K p 0) (fun i=>((A i).unmasked_cont 0).measurable) cap
  have same (U) : f U=(∑'i,masked (R.family.path.rep N per j).p.threshold (X i) (Gf i) (v.view U))-
      ∑'i,Gf i (v.view U) := by
    dsimp only [f,maskedGram,Gf,A,X]
    congr 1
    apply tsum_congr
    intro i
    unfold Low.maskedPlain
    rw [←hp]
    by_cases h : Healthy p.threshold ((gramLow i).home K p 0) (v.view U)
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h,gram_plain]
    · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]
  rw [funext same]
  convert tst using 1 <;> simp only [Seat.view,Pi.sub_def,fee,C,mul_one,Nat.cast_ofNat]
  norm_num

end YM.Integration.OriginalMarkedRunAction
