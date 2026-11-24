import YM.MS.ScaleForest.Icy
/-!
# Allow the line types to be separately accounted

A palette holds the complete set with multiplicities; its criterion for
sharing the same prescription is an EXACT symbolic identity, on every
leg and every momentum in the continuation. When graph kernels are summed
over these choices, get precisely the A0 sewing and its dimensional measure.
This will let us calculate everything in one palette and still justify
alternative groupings of the diagrams (as series, not just rank 2).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {b : Bool} {X Y : Flats G}

structure Palette (G : Gauge) where
  lines : List (LineRule G)
  quality : (lines.map LineRule.half).sum = A0 G 0

def heatLines (G : Gauge) : Palette G := ⟨[fullShell G], List.sum_singleton⟩

private theorem tree_add (A B : Rip G) (X Y : Flats G) : TreeN (A+B) X Y= TreeN A X Y+TreeN B X Y := by
  unfold TreeN; simp_rw [explodeL,Finsupp.sum]
  have he (i j : ℕ) : tapeB (squad (A+B)) (X i) (Y j)= tapeB (squad A) (X i) (Y j)+tapeB (squad B) (X i) (Y j) :=
    funext fun _ => two_leg ..
  simp only [he, Finsupp.single_add, Finset.sum_add_distrib]

theorem tree_zero (X Y : Flats G) : TreeN 0 X Y=0 := by
  have he := tree_add 0 0 X Y; rw [add_zero] at he
  exact add_eq_left.mp he.symm

theorem sum_bridge (P : Palette G) (A B : Flats G) :
    (P.lines.map (fun K=> bridgePages K.half A B)).sum= drive0 G A B := by
  simp_rw [show ∀ K:LineRule G,bridgePages K.half A B=TreeN K.half A B from fun K=>bridgePages_eq K.ok.rev _ _]
  unfold drive0; rw [← P.quality]
  generalize P.lines=L
  induction L with
  | nil=> simp [tree_zero]
  | cons i L ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,tree_add,ih]

theorem sum_connect (P : Palette G) (b : Bool) (X Y : Flats G) :
    (P.lines.map (fun K=> connect b K X Y)).sum=(factor b:ℂ) • drive0 G X Y := by
  unfold connect; rw [← sum_bridge P]; generalize P.lines=L
  induction L with
  | nil=> simp
  | cons i L ih=> simp only [List.map_cons,List.sum_cons,ih,smul_add]

private theorem cycle_add {U V : Rip G} (h : Knot b U) (he : Knot b V) (hX : Moony b X) :
    Pact (CycleN (U+V) X) (CycleN U X+CycleN V X) := by
  intro i
  filter_upwards [Moony.sunup hX,high0] with z hz ht
  unfold CycleN; rw [Finsupp.add_apply, Pi.add_apply]; simp_rw [blap,Finsupp.sum,
    Finsupp.finsetSum_apply, Finset.sum_apply]; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj=> ?_
  rw [Finsupp.single_apply,Finsupp.single_apply,Finsupp.single_apply]; split
  · rw [swamp_spec (h.add he) (hz j) ht, swamp_spec h (hz j) ht, swamp_spec he (hz j) ht,
      oceanL h (hz j) he ht,smul_add]
  simp

private theorem cycle_zero (hX : Moony b X) : Pact (CycleN 0 X) 0 := by
  have ht := cycle_add (Knot.zero (G:=G)) (Knot.zero (G:=G)) hX
  rw [zero_add] at ht
  intro i; filter_upwards [ht i] with z hz
  rw [Finsupp.add_apply,Pi.add_apply] at hz; exact add_eq_left.mp hz.symm

theorem combine_loop (P : Palette G) (X : Flats G) (hX : Moony b X) :
    Pact (P.lines.map (fun K=> closePages K.half X)).sum (step0 G X) := by
  unfold step0; rw [← P.quality]; generalize P.lines=L
  have he (L : List (LineRule G)) : Knot b (L.map LineRule.half).sum := by
    induction L with
    | nil=> exact Knot.zero
    | cons i L ih=> exact (i.ok.forms b).add ih
  induction L with
  | nil=> exact pact_sym (cycle_zero hX)
  | cons i L ih=>
    rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons]
    exact pact_comp
      (common (closePages_pact (i.ok.forms _) hX) ih) (pact_sym (cycle_add (i.ok.forms _) (he L) hX))
end YM.MS.ScaleForest
