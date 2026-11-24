import YM.MS.ScaleForest.CloseBlock

/-!
# All ordered bridge-branch possibilities and loop extensions from them

Primaries are either vertices or bridges. Provide the proof that including
all entries in the palette and zero-or-more residual loop extensions implements
Bob, using these actual multiplicities. There is no planar-skeleton assumption in this
sum. Some entries of the list can be zero (including if no free half-edges
are actually available). We do use dimension and ghost/color information at
every step in the integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {b : Bool}

abbrev Computes (L : Hist G b h) (Z : Flats G) (W : Coat G) := ∃ r : ℤ,
    Bob b h 0 r Z (renHistory L) W (poleHistory L)

namespace Computes

theorem nil (G : Gauge) (b : Bool) (h : ℕ) : Computes ([]: Hist G b h) 0 0 := ⟨0,block_zero ..⟩

theorem app {L M : Hist G b h} {z x : Flats G} {f g : Coat G} (ht : Computes L z f) (hy : Computes M x g) :
    Computes (L++M) (z+x) (f+g) := by
  obtain ⟨u,hU⟩:=ht; obtain ⟨v,hV⟩:= hy; unfold Computes; rw [ren_append,pole_append];
  exact ⟨_,block_plus (block_raise hU (le_max_left u v)) (block_raise hV (le_max_right u v))⟩

theorem sums {I : Type} (f : I → Hist G b h) (L : List I) {v : I → Flats G} {w : I→Coat G}
    (hv : ∀ i∈L, Computes (f i) (v i) (w i)) : Computes (L.flatMap f) (L.map v).sum (L.map w).sum := by
  induction L with
  | nil=> exact nil ..
  | cons i L ih=>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons]; exact (app (hv i (by simp))
      (ih (fun i hi=> hv i (List.mem_cons_of_mem _ hi))))
end Computes

variable (P : Palette G)

def pairBranch (A : GraphSum G true 4) (B : GraphSum G b h) :=
  P.lines.flatMap fun K=>spiraling P (bridge K A B)

def everyBridge (L : Hist G true 4) (M : Hist G b h) :=
  L.flatMap (fun A=> M.flatMap (pairBranch P A))

theorem pair_computes (A : GraphSum G true 4) (B : GraphSum G b h) :
    Computes (pairBranch P A B) ((factor b : ℂ) • drive0 G A.instructions.renorm B.instructions.renorm) 0 := by
  rw [← sum_connect P]
  have hv := Computes.sums (w:=fun _=>0) (v:=fun K=> connect b K A.instructions.renorm B.instructions.renorm)
      _ P.lines (fun K _=> ⟨ (bridge K A B).slots, spire_block P (bridge K A B)⟩)
  simpa only [pairBranch,show (P.lines.map (fun _=> (0:Coat G))).sum = 0 by simp] using hv

theorem right_computes (A : GraphSum G true 4) (M : Hist G b h) :
    Computes (M.flatMap (pairBranch P A)) ((factor b:ℂ) • drive0 G A.instructions.renorm (renHistory M)) 0 := by
  induction M with
  | nil=> simp only [ren_nil,map_zero,smul_zero]; exact Computes.nil ..
  | cons B M ih=>
    rw [List.flatMap_cons,ren_cons,map_add,smul_add]; simpa only [add_zero] using
      Computes.app (pair_computes P A B) ih

theorem every_computes (L : Hist G true 4) (M : Hist G b h) :
    Computes (everyBridge P L M) ((factor b:ℂ) • drive0 G (renHistory L) (renHistory M)) 0 := by
  induction L with
  | nil=> simp only [ren_nil,map_zero, LinearMap.zero_apply,smul_zero]; exact Computes.nil ..
  | cons i L ih=>
    rw [show everyBridge P (i::L) M=(M.flatMap (pairBranch P i))++ everyBridge P L M from rfl,
        ren_cons,map_add,LinearMap.add_apply,smul_add]; simpa only [add_zero] using Computes.app (right_computes P i M) ih

theorem primary_computes (A : LocalVertex G b h) : Computes (spiraling P (vertex A)) 0 (fun _ : ℂ=>A.symbol) :=
  ⟨_, spire_block P (vertex A)⟩
end YM.MS.ScaleForest
