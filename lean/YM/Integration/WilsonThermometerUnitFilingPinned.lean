import YM.Integration.WilsonMarkedIndependentNormalizedRecursion
import YM.Integration.WilsonThermometerUnitFilingWeakStrip
import YM.WilsonCoeffUV.Marked.Bounds.Penalty

/-! The complete angular ordinary source after its actual capture, on one fixed set of addresses. Each older date uses the original unmarked story in the normalized one-source operator. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinned
open Function Filter Finset Lattice Laurent RG Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open Precision Input WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Shard WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {W:Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def march (A:Levels G)(O:ChartRatio G)(N b v height:ℕ)(X:Era G W):Era G W:=
  if edge:v<b then verseI A O v N height (march A O N b (v+1) height X) else X
termination_by b-v
decreasing_by omega

theorem top (A:Levels G)(O:ChartRatio G)(N b height:ℕ)(X:Era G W):
    march A O N b b height X=X:=by rw [march,dif_neg (lt_irrefl _)]

theorem step (A:Levels G)(O:ChartRatio G)(N b v height:ℕ)(X:Era G W)(edge:v<b):
    march A O N b v height X=verseI A O v N height (march A O N b (v+1) height X):=by
  rw [march,dif_pos edge]

variable [CompleteSpace W]

theorem enrolled (A:Levels G)(O:ChartRatio G){N b v h:ℕ}{X:Era G W}(auth:Auth h X)
    (simple:G.Simple)(ratio:LocalRatio O)(bn:b ≤ N)(vb:v ≤ b):
    Auth h (march A O N b v h X):=by
  induction vb using Nat.decreasingInduction with
  | self=> rwa [top]
  | of_succ i live ih=>rw [step _ _ _ _ _ _ _ live];exact Auth.verse A (live.trans_le bn) simple ratio ih

theorem sum {J:Type} [Fintype J] (A:Levels G)(O:ChartRatio G){N b v height:ℕ}
    (simple:G.Simple)(ratio:LocalRatio O)(bn:b≤N)(vb:v≤b)(Z:J→Era G W)(stock:∀j,Auth height (Z j)):
    march A O N b v height (∑j:J,Z j)=∑j:J,march A O N b v height (Z j):=by
  induction vb using Nat.decreasingInduction with
  | self=>simp only [top]
  | of_succ i live ih=>
    rw [step _ _ _ _ _ _ _ live,ih]
    have quoted:=verse_sum A (d:=fun _:J=>(1:ℝ)) (S:=univ) simple (live.trans_le bn) ratio
      (fun j _=>enrolled A O (stock j) simple ratio bn (Nat.succ_le_of_lt live))
    simpa only [one_smul,step A O N b i height _ live] using quoted

variable {I:Type} [Fintype I] {V:I→Type}
variable [∀i,NormedAddCommGroup (V i)] [∀i,NormedSpace ℝ (V i)] [∀i,CompleteSpace (V i)]

theorem filed (A:Levels G)(O:ChartRatio G){N b v height:ℕ}(simple:G.Simple)(ratio:LocalRatio O)
    (bn:b ≤ N)(vb:v ≤ b)(X:(i:I)→Era G (V i))(grade:I→ℕ)(read:(i:I)→V i→L[ℝ]W)(weight:I→ℝ)
    (auth:∀i,Auth (grade i) (X i))(cap:∀i,grade i ≤ height):
    march A O N b v height (∑i:I,weight i • tuftV (read i) (X i)) =
      ∑i:I,weight i • tuftV (read i) (march A O N b v (grade i) (X i)):=by
  induction vb using Nat.decreasingInduction with
  | self=>simp only [top]
  | of_succ j live ih=>
    have booked (i:I):=enrolled A O (auth i) simple ratio bn (Nat.succ_le_of_lt live)
    rw [step _ _ _ _ _ _ _ live,ih,verse_sum A simple (live.trans_le bn) ratio
      (fun i _=>((booked i).tuft (read i)).tall (cap i))]
    apply sum_congr rfl;intro i _
    rw [step _ _ _ _ _ _ _ live,ply_verse A (live.trans_le bn) simple ratio (booked i)]
    exact congrArg (fun u:Era G W=>weight i • u) (verseExpand A (live.trans_le bn) simple ratio
      ((booked i).tuft _) (cap i)).symm

variable {ι:Type} [DecidableEq ι] {D:ι→ℕ}

theorem original (R:Run G)(simple:G.Simple){N b v height:ℕ}(bn:b ≤ N)(vb:v ≤ b)
    (K k:ι→ℕ)(X:I→Outerm G D)(stock:∀i,Wellness k (X i))(mask:I→Finset ι)
    (seat:I→ι→ Cover)(read:(i:I)→Pen D (mask i)→L[ℝ]W)(weight:I→ℝ)
    (cap:∀i,mass k (mask i) ≤ height):
    let A:=R.family.path.levels
    let O:=R.metals.O
    let row:=fun i=>levelsO ((Gears A O K k N N b (X i)) (seat i)) (mask i)
    march A O N b v height (∑i:I,weight i • tuftV (read i) (row i)) =
      ∑i:I,weight i • tuftV (read i) (march A O N b v (mass k (mask i)) (row i)):=by
  intro A O row
  letI : ∀i:I,CompleteSpace (Pen D (mask i)):=fun i=>by
    change CompleteSpace (WilsonCoeffUV.Wheel.Table D (mask i) →L[ℝ]ℝ)
    infer_instance
  apply filed A O simple R.alloy.B.ratio bn vb row _ read weight _ cap
  intro i
  have live:=Cog (K':=K) A O (N:=N) (b:=N) le_rfl (X i) (stock i) simple R.alloy.B.ratio bn
  exact placedO _ (live.level' _) _

end YM.Integration.WilsonThermometerUnitFilingPinned
