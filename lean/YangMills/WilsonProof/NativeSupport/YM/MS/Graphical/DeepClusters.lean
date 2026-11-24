import YM.MS.Graphical.DeepClusters
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.PricePin

/-!
# Graph closures on a connected multi-pin

No final local counterterms here (separated prescription only!); keep adding
ordered self-pairs until exhausted, just as for the single-root diagrams. Sum
of possible runs at the rank budget (actually has padding by zeros). Native
spine NOT used in this definition. Lines, sector UV analytics and first
single-root preparations are inputs through the `F`s.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I : Type} {t v u w a R : ℝ} {m n : ℕ} {q k j : ℤ} {G : Gauge} {x : Tone.QP}
variable {F H X Y : Schedule G} {z : ℂ} {b c : Bool}


namespace Countered
lemma adds_range (h : Countered true q F) (y : ℝ) (n : ℕ) : Countered true (q-2*n) (runCloses y F n) := by
  induction n with
  | zero=> simpa [runCloses] using h.top
  | succ n ih=>rw [runCloses,iterate_succ_apply', show q- (2:ℤ)*(n+1:ℕ)=q-2*n-2 by omega]; exact (ih.closeT y).top
lemma poses (h : Countered true q F) (y : ℝ) (n : ℕ): Countered true q (pinTower y F n) :=
  sum (Finset.range _) fun i _=> (h.adds_range y i).up (by omega)
lemma final_poses (h : Countered true q F) (y : ℝ) (hn : q ≤ (n:ℤ)) {i:ℕ} (hp : n ≤ i) :
    TimeEq (closeAt y (runCloses y F i)) 0 ∧ regularPart (closeAt y (runCloses y F i))=0 :=
  ((h.adds_range y i).closeT y).runsOut (by omega)
lemma padding (h : Countered true q F) (y : ℝ) (hn : q ≤(n:ℤ)) {i:ℕ} (hp : n < i) :
    TimeEq (runCloses y F i) 0∧regularPart (runCloses y F i) =0:=
  (h.adds_range y i).runsOut (by omega)
end Countered

open Rake Latch Job Geo Breeze

def at4 (F : Schedule G): Glade G Unit := fun _ t=> regularPart F t 0
abbrev pinOperator (G : Gauge) := sailP (fun _ : Unit => Osc.Snap.planeF) (constantP G Unit (PlanetD G))

lemma enoughRoom (h : Countered b (n:ℤ) F) : collect (at4 F) := ⟨ n,fun _ t=>(h.foot t).1 0 ⟩
lemma at4_zero : at4 (0:Schedule G)=0:= by unfold at4; rw [regularPart_zero]; rfl
lemma at4_sum (S : Finset I) (F : I→ Schedule G) (h : ∀ i∈S, Countered b q (F i)) :
    at4 (∑ i∈S,F i)=∑ i∈ S, at4 (F i) := by unfold at4; rw [sum_payment S h]; ext; simp only [Finset.sum_apply]
lemma at4_add (h : Countered b q F) (hp : Countered c k H) : at4 (F+H)=at4 F+at4 H:= by
  unfold at4; rw [sum_progress h hp]; rfl
lemma cycle_before4 (h : Countered true q F) (y : ℝ) : at4 (closeAt y F)=pinOperator G (at4 F):= by
  funext i t; unfold at4; rw [close_payment h,canon_at_zero _ _ (h.foot t).2]
lemma cycle_pre' (h : Countered true q F) (i : Unit) (t : ℝ) : pinOperator G (at4 F) i t=deep G t (at4 F i t):= by
   rw [← cycle_before4 h 0]; unfold at4; rw [close_payment h, canon_at_zero' _ _ (h.foot t).2]
lemma integral_before4 (h : Countered true q F) : at4 (integratePins F)=river (at4 F):= by
   funext i t; unfold at4; rw [integral_payment h]; rfl
lemma cycleAt_sum (S : Finset I) (F : I→ Schedule G) (h : ∀ i∈S, Countered true q (F i)) :
    pinOperator G (at4 (∑ i∈ S,F i))=∑ i∈S, pinOperator G (at4 (F i)) := by
  funext i t; rw [cycle_pre' (Countered.sum S h),at4_sum S F h];
  simp only [Finset.sum_apply,map_sum]
  exact Finset.sum_congr rfl fun j hj=> (cycle_pre' (h j hj) i t).symm

lemma train_yes (h : Countered true q F) : train false (at4 F) := fun _ t w _=> h.trains t 0 w
lemma cycle_yes (h : Countered true q F) (y : ℝ) : train false (pinOperator G (at4 F)) := by
  rw [← cycle_before4 h y]; exact train_yes (h.closeT y)


section sum
variable {A : I→ Glade G Unit} (S : Finset I) (h : ∀ i∈S,train false (A i))
lemma train_two (X Y : Glade G Unit) (h : train false X) (hp : train false Y) : train false (X+Y) :=
   fun i t w he=> (h i t w he).add (hp i t w he)
include h
private lemma flow_pin : train false (∑ i∈ S,A i) := by
   classical
   induction S using Finset.induction with
   | empty=> rw [Finset.sum_empty]; exact fun i t w _=> integrable_zero _ _ _
   | insert i S hi ih=> rw [Finset.sum_insert hi]; exact train_two _ _ (h i (by simp)) (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
private lemma flow_mass : river (∑ i∈ S,A i)=∑ i∈S,river (A i):= by
  classical
  induction S using Finset.induction with
  | empty=>simp [river0]
  | insert i S hi ih=>
    obtain hp: ∀ i∈ S, train false (A i) := fun _ hi=>h _ (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, flow_add (h i (by simp)) (flow_pin S hp), ih hp]
end sum

/-- At the needed rank budget the tower exhausts the joins; its specialization
gives exactly the 4-dimensional `Trip` length recursion. -/
theorem integrate_every_edge (h : Countered true (n:ℤ) F) (y : ℝ) :
    Trip (pinOperator G) (at4 (pinTower y F n)) (at4 F) := by
  let x i:= runCloses y F i; have H(i:ℕ) : Countered true (n:ℤ) (x i):= (h.adds_range y i).up (by omega)
  have he := h.poses y n
  refine ⟨enoughRoom he, train_two _ _ (cycle_yes he y) (train_yes h),?_⟩
  rw [flow_add (cycle_yes he y) (train_yes h)]; unfold pinTower
  rw [cycleAt_sum _ _ (fun i _=> H i),at4_sum _ _ (fun i _=>H i),flow_mass _ (fun i _=>cycle_yes (H i) y)]
  have hz : pinOperator G (at4 (x n)) = 0:= by
     rw [← cycle_before4 (H n) y]; unfold at4; rw [(h.final_poses y le_rfl (Nat.le_refl n)).2]; rfl
  conv_rhs=> lhs; rw [Finset.sum_range_succ]
  conv_lhs=> rw [Finset.sum_range_succ']
  rw [hz,river0, add_zero]; refine congr_arg₂ (·+·) (Finset.sum_congr rfl (fun i _=>?_)) (integral_before4 h)
  rw [← cycle_before4 (H i) y, ← integral_before4 ((H i).closeT y)]; change at4 (runCloses _ _ _)= _; rw [runCloses, iterate_succ_apply']; rfl
end YM.MS.Graphical
