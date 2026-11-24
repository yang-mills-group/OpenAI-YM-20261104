import YM.Integration.WilsonPositionProgramTrialNestedCenters
import YM.Integration.WilsonPositionProgramTrialPatchCenter

/-! The sampled original f-grid word is planted on the separately purchased
K-mesh. Its own child digit at each site is retained under a common
older-cell reduction. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialHomeCenters
open Finset Lattice WilsonCoeffUV.Bank
open WilsonPositionProgramTrialCellDigits WilsonPositionProgramTrialPatchCenter
open scoped Classical
variable {I : Type}

theorem odd (S : Schedule) (m q : ℕ) : Odd (S.steps m q).val := by
  induction q with
  | zero => exact odd_one
  | succ q ih => exact ih.mul (S.block_odd (m+q))

def plant (S : Schedule) {f K : ℕ} (cut : f ≤ K) (o : I → Cover)
    (digit : I → Site (S.toDepth cut 0).count) : I → Cover :=
  fun i => (S.toDepth cut 0).count.val • o i+lift (digit i)

theorem parent (L : Side) (x : Cover) (d : Site L) :
    parentC L (L.val • x+lift d)=x :=
  congrArg Prod.fst ((panel L Unit).symm_apply_apply (x,d,()))

theorem original (S : Schedule) {w f K : ℕ} (before : w ≤ f) (cut : f ≤ K)
    (o : I → Cover) (digit : I → Site (S.toDepth cut 0).count)
    (pivot : Cover) (own : Site (S.toDepth cut 0).count) :
    moved S (before.trans cut) ((S.toDepth cut 0).count.val • pivot+lift own) (plant S cut o digit) =
      plant S cut (moved S before pivot o) digit := by
  let A:=(S.toDepth before 0).count
  let B:=(S.toDepth cut 0).count
  let C:=(S.toDepth (before.trans cut) 0).count
  have size : C.val=B.val*A.val :=
    Next.Rank.Station.size_comp (S.toDepth before 0) (S.toDepth cut 0) _
  have anchor : parentC C (B.val • pivot+lift own)=parentC A pivot := by
    rw [WilsonPositionProgramTrialNestedCenters.combine A B C size (odd S w (f-w)),parent]
  funext i
  change B.val • o i+lift (digit i)-C.val • parentC C (B.val • pivot+lift own)=
    B.val • (o i-A.val • parentC A pivot)+lift (digit i)
  rw [anchor,size,mul_smul,smul_sub]
  abel

theorem physical (S : Schedule) {f K : ℕ} (cut : f ≤ K) (o : I → Cover)
    (digit : I → Site (S.toDepth cut 0).count) (i : I) :
    S.gridPoint K (plant S cut o digit i)=S.gridPoint f (o i)+S.gridPoint K (lift (digit i)) ∧
      ‖S.gridPoint K (lift (digit i))‖≤S.a f := by
  constructor
  · ext a
    change S.a K * ((((S.toDepth cut 0).count.val • o i a:ℤ)+lift (digit i) a:ℤ):ℝ)=
      S.a f*(o i a:ℝ)+S.a K*(lift (digit i) a:ℝ)
    rw [Int.cast_add,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,mul_add,
      ←mul_assoc,S.embeds_scale]
  · let x (_ : Unit) := lift (digit i)
    have h:=WilsonPositionProgramTrialCenterHousing.anchor_bound S cut x ()
    rw [pivot] at h
    simpa only [x,wrap_lift] using h

end YM.Integration.WilsonPositionProgramTrialHomeCenters
