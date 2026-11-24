import YM.MS.Motif.Plateau
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Matrix
/-!
# Preparations. Unstar arbitrary differentiated fields, Cartan.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open scoped Topology ContDiff InnerProductSpace
variable {A:Type}{G:Gauge}{n:ℕ}{b c:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 " ⋄ "=> product S
variable {F X:Rack G n} {U H W : Mield G n}
-- derivative color-level.
-- trace of commutator against first factor = 0 (gauge Ω), when X even (moves commuting)
lemma ground (h:un U false): (∑ i:G.ColorIndex, (jaw G n U H i) ⋄ U i)=0:= by
    simp only [chew,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; let X(i j k:G.ColorIndex):= (rune j k i) • ((U j⋄ H k ) ⋄ U i); let D:= ∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex,X i j k; have hc:D= -D:= by
       unfold D; nth_rw 1 [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>?_; unfold X; rw [r_clock i k j,r_ortho k j,neg_smul]; congr! 2; rw [(h i).central (H k), (h j).central (H k),times_assoc (p:=S) (H k) (U i) (U j),times_assoc (p:=S) (H k) (U j) ( U i ), (h i).central (U j) ]
    change D=0; ext x; obtain hp := congr_fun hc x; rw [Pi.neg_apply] at hp; change D x=0; exact add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp hp.symm)
end YM.MS.Motif
