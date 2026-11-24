import YM.RG11Proof.Rigidity.Lists
import YM.RG11Proof.Rigidity.Rotor

/-!
# Pigment words (real)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff Classical

structure Dart (G : Gauge) where
  degree : ℕ
  tone : G.ColorIndex
  mode : Flavor degree

variable {G : Gauge}

def Dart.flip (a : Dart G) : Free.Factor G := ⟨a.degree,flavor a.degree a.tone a.mode⟩
def Dart.write (a : Dart G) := Free.letter a.flip

structure Pig (G : Gauge) where
  origin : E4
  dart : Dart G

def Pig.full (a : Pig G) : Limb G := (a.origin,a.dart.flip)

abbrev Seeker (G : Gauge) := G.ColorIndex → Pig G

-- Don't concoct a covariance for fake coalesced observables: this
-- always has the zero-same-point Wick-list convention.
def line (a b : Pig G) : ℝ := if a.origin=b.origin then 0 else
   legKernel a.dart.flip.2 b.dart.flip.2 (a.origin-b.origin)

lemma line_eq (a b : Pig G) : (line a b : ℂ)=linkEntry a.full b.full := by
  by_cases he : a.origin=b.origin <;> simp [line,linkEntry,Pig.full,K,he]

lemma line_sym (a b : Pig G) : line a b=line b a := by
  unfold line; by_cases he : a.origin=b.origin
  · rw [if_pos he,if_pos he.symm]
  rw [if_neg he,if_neg (Ne.symm he), ← neg_sub a.origin b.origin]
  exact Maxwell.exchange _ _ (sub_ne_zero.mpr he)

def toss (a : Foil) (y : E4) : Seeker G := fun c=> ⟨y,0,c,cell a.1 a.2⟩

def beam (x : E4) (a b : Foil) := if x=0 then 0 else 4*normal*(qRad x)⁻¹^3 * rotor x a b
lemma toss_line (a b : Foil) (y z : E4) (c u : G.ColorIndex) :
    line (toss a y c) (toss b z u)= if c=u then beam (y-z) a b else 0 := by
  by_cases he : y=z
  · simp [he,line,toss,beam]
  rw [beam,if_neg (sub_ne_zero.mpr he)]
  unfold toss line Dart.flip
  rw [if_neg he]; exact foilPrice a b _ _ c (sub_ne_zero.mpr he)
lemma toss_dead (a : Foil) (ha : a.1=a.2) (y : E4) (c : G.ColorIndex) (i : Pig G) :
    line (toss a y c) i=0 := by
  change (if y=i.origin then 0 else legKernel (flavor 0 c (cell a.1 a.2)) i.dart.flip.2 (y-i.origin))=0
  split_ifs with h
  · rfl
  rw [ha,noFoil,map_zero]
  exact map_zero ((pairing (G:=G) (show y-i.origin ∈ away from sub_ne_zero.mpr h)).flip _)

abbrev Word (G : Gauge) := List (Pig G)
abbrev meter (L : Word G) := pairCost line L
lemma meter_full (L : Word G) : (meter L : ℂ) = pairCost linkEntry (L.map Pig.full) := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
    cases L with
    | nil => simp [meter,pairCost]
    | cons a L =>
      change ((↑(pairCost line (a::L)):ℂ))=_
      rw [pair_step,List.map_cons,pair_step,pulls_map]
      unfold pulls; push_cast
      apply Finset.sum_congr rfl; intro i _
      rw [line_eq a]
      congr 1; apply ih _ (by rw [← h]; exact lt_trans (pulls_short _) (by simp)) _ rfl

lemma meter_perm {L T : Word G} (h : L.Perm T) : meter L=meter T := pair_perm line line_sym h

end YM.RG11.Rigidity
