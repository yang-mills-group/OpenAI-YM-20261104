import YM.Integration.WilsonCenteredNestedPairChord
import YM.Integration.WilsonThermometerWeakPairRooms

/-! The real three-field deposited tree is an original raw convoy,
including its freely specified child center and the separate parent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairConvoy
open Finset Filter Function Spec Table OPE OPE.Arboreal OPE.Nesting OPE.Nesting.Tree
open WilsonCenteredNestedTwoVertex WilsonThermometerWeakPairFork
open scoped Classical Topology BigOperators

def sites (z : full.Plot) : Fin 5→E4 :=
  ![anchor z,skyline z 0,skyline (childPlace 0 z) 0,skyline (childPlace 0 z) 1,skyline z 1]

private lemma tip {i j : Fin 5} (single : i∉frame.zones) (ancestry : frame.Anc i j) : i=j := by
  by_contra ne
  exact single (ancestry.proper (Ne.symm ne))

private lemma inside {j : Fin 5} (ancestry : frame.Anc 1 j) : j=1 ∨ j=2 ∨ j=3 := by
  fin_cases j
  · exact ((show (1:Fin 5)≠0 by decide) ancestry.excess).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · have e := ancestry.into (by decide)
    change (1:ℕ)<1 at e
    omega

/-- Both original branch placements come from the same qualified Nesting plot. -/
theorem original {r a M η : ℝ} {z : full.Plot} (Mn : 0 ≤ M) (ok : Accept r M η (dates r a) z) :
    frame.Convoy M η (radius a r) (sites z) := by
  have ht := ok.levels
  have relative := ok.relative
  have near := relative.2.2 (0:Fin 2)
  have ar : a≤r := by
    have e :a≤r*1 := (ht.2.2 (0:Fin 2)).2.1
    rwa [mul_one] at e
  have rp : 0<r := ht.1
  have ap : 0<a := (ht.2.2 (0:Fin 2)).1
  have far (j:Fin 5)(ancestry:frame.Anc 1 j) : η*r ≤ ‖sites z j-sites z 4‖ := by
    rcases inside ancestry with rfl|rfl|rfl
    · exact relative.2.1 (0:Fin 2) 1 pair.topSeat (arms 1).topSeat (by decide)
    · exact relative.2.1 (0:Fin 2) 1 (.inr ⟨0,()⟩) (arms 1).topSeat (by decide)
    · exact relative.2.1 (0:Fin 2) 1 (.inr ⟨1,()⟩) (arms 1).topSeat (by decide)
  have nearSep : η*a ≤ ‖sites z 2 - sites z 3‖ := near.2.1 (0:Fin 2) 1 () () (by decide)
  have kid0 : frame.kids 0={1,4} := by ext j;fin_cases j <;> simp [Arboreal.kids,frame]
  have kid1 : frame.kids 1={2,3} := by ext j;fin_cases j <;> simp [Arboreal.kids,frame]
  constructor
  · constructor
    · intro i hi
      rcases (by simpa [frame] using hi : i=0 ∨ i=1) with rfl|rfl
      exacts [rp,ap]
    · intro i hi
      rcases (by simpa [frame] using hi : i=0 ∨ i=1) with rfl|rfl
      exacts [le_rfl,ar]
  · intro j
    fin_cases j
    · change ‖anchor z-anchor z‖≤M*r
      simpa using mul_nonneg Mn rp.le
    · exact relative.1 (.inr ⟨0,pair.topSeat⟩)
    · exact near.1 (.inr ⟨0,()⟩)
    · exact near.1 (.inr ⟨1,()⟩)
    · exact relative.1 (.inr ⟨1,()⟩)
  · intro i j k split
    have live := split.inner
    obtain ⟨v,hv,w,hw,diff,hj,hk⟩ := split
    rcases (by simpa [frame] using live : i=0 ∨ i=1) with rfl|rfl
    · rw [kid0] at hv hw
      rcases (by simpa using hv : v=1∨v=4) with rfl|rfl <;>
        rcases (by simpa using hw : w=1∨w=4) with rfl|rfl
      · exact (diff rfl).elim
      · rw [←tip (by decide : (4:Fin 5)∉frame.zones) hk];exact far _ hj
      · rw [←tip (by decide : (4:Fin 5)∉frame.zones) hj,norm_sub_rev];exact far _ hk
      · exact (diff rfl).elim
    · rw [kid1] at hv hw
      rcases (by simpa using hv : v=2∨v=3) with rfl|rfl <;>
        rcases (by simpa using hw : w=2∨w=3) with rfl|rfl
      · exact (diff rfl).elim
      · rw [←tip (by decide : (2:Fin 5)∉frame.zones) hj,←tip (by decide : (3:Fin 5)∉frame.zones) hk]
        exact nearSep
      · rw [←tip (by decide : (3:Fin 5)∉frame.zones) hj,←tip (by decide : (2:Fin 5)∉frame.zones) hk,norm_sub_rev]
        exact nearSep
      · exact (diff rfl).elim

lemma rotated {I : Type} [Fintype I] {T : Arboreal I} {s : I→ℝ} {x : I→E4} {M η : ℝ}
    (cal : T.Convoy M η s x) (k : Ortho) : T.Convoy M η s (Ortho.move k ∘ x) := by
  constructor
  · exact cal.sizes
  · intro i
    change ‖Ortho.motion k (x i)-Ortho.motion k (x (T.parent i))‖ ≤ _
    rw [←map_sub]
    change ‖Ortho.move k (x i-x (T.parent i))‖ ≤ _
    rw [Ortho.move_norm]
    exact cal.travel i
  · intro i j l h
    change _ ≤ ‖Ortho.motion k (x j)-Ortho.motion k (x l)‖
    rw [←map_sub]
    change _ ≤ ‖Ortho.move k (x j-x l)‖
    rw [Ortho.move_norm]
    exact cal.spread _ _ _ h

end YM.Integration.WilsonCenteredNestedPairConvoy
