import YM.MSbar.Pole.Feynman.Divide
/-! Calculate support and flow weights for the induction on graphs. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman
open Set Function Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread
open scoped Topology ContDiff BigOperators Classical
variable {I V : Type}

namespace Chart
variable (C:Chart I V) {X Y S:Finset I}
lemma hands_exterior (h:S ⊆ C.mom): Disjoint (C.hands S) C.mom:= by
  refine Finset.disjoint_left.mpr fun k hk hx=> ?_
  obtain ⟨i,hi,hg⟩:=Finset.mem_biUnion.mp hk
  exact Finset.disjoint_left.mp (C.separate i (h hi)) hg hx
lemma hands_separate (hx : X⊆ C.mom) (hy : Y⊆ C.mom) (hp:Disjoint X Y):Disjoint (C.hands X) (C.hands Y):=by
  refine Finset.disjoint_left.mpr fun k hk hk'=> ?_
  obtain ⟨i,hi,hg⟩:=Finset.mem_biUnion.mp hk; obtain ⟨j,hj,hG⟩:=Finset.mem_biUnion.mp hk'
  have he:i≠j:=fun hh=>Finset.disjoint_left.mp hp hi (hh.symm ▸ hj)
  exact Finset.disjoint_left.mp (C.unique i j (hx hi) (hy hj) he) hg hG
end Chart

namespace District
variable (D:District I V) (C:Chart I V)
def opens := C.hands (D.mouths C)
def weight := (∑ i∈D.mouths C,C.age i)-4
def leader [Nonempty I] := if h:(D.mouths C).Nonempty then h.choose else Classical.arbitrary I
def view [Nonempty I]:= ((D.mouths C).erase (D.leader C)) ∪ D.opens C
def thread [Nonempty I](e:I×I):Thread I:= ⟨D.mouths C,D.leader C,e.1,e.2,C.chain e,C.constant e⟩
lemma borders : D.mouths C ⊆ C.mom:=fun i hi=> (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
variable {D C} {S:Finset V} {e:I×I}
namespace Clear
variable [Nonempty I] (h:D.Clear C)(he:e∈D.paths)
include h
lemma chief : D.leader C∈D.mouths C:=by unfold leader; rw [dif_pos h.mouths]; exact h.mouths.choose_spec
lemma notations : Disjoint C.mom (D.opens C):= (C.hands_exterior (D.borders C)).symm
include he
local notation "X" => D.thread C e
lemma fresh : e.1∉ D.mouths C ∧ e.2∉D.mouths C:= ⟨fun hx=> (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩), fun hx=> (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)⟩
lemma sameMark : (X).inputs=(D.less e).mouths C := (h.benefit he).symm
lemma corresponds : (X).chain.reads ∪ D.opens C=(D.less e).opens C:=by
  unfold opens; rw [h.benefit he, thread]
  simp only [Chart.hands,Finset.biUnion_insert,(C.budget e (h.isPair he)).2.1,Finset.union_assoc]
lemma permission : (X).Fits (D.opens C):= by
  obtain ⟨hl,hp,hq,hj⟩:= h.boundary e he; obtain ⟨hv,hy,hx⟩:= C.budget e hj
  obtain ⟨ha,hb⟩:=h.fresh he
  refine ⟨h.chief,hl,ha,hb,?_,?_,hv⟩
  · have ht : (X).chain.reads = C.hands ({e.1,e.2}) := by unfold thread; rw [hy]; simp [Chart.hands]
    rw [ht]
    have hset : ({e.1,e.2} : Finset I) ⊆ C.mom:= by
      intro i hi; simp at hi; rcases hi with hi|hi; rw [hi]; exact (Finset.mem_filter.mp hp).1; rw [hi]; exact (Finset.mem_filter.mp hq).1
    exact C.hands_separate hset (D.borders C) (by simp [ha,hb])
  rw [sameMark h he,corresponds h he]; exact ((C.hands_exterior ((D.less _).borders C)).symm).mono_left ((D.less e).borders C)
lemma unmoored : Disjoint C.mom ((X).chain.reads ∪ D.opens C):=by rw [corresponds h he]; exact (C.hands_exterior ((D.less e).borders C)).symm
lemma counting : D.weight C=(D.less e).weight C-2-(X).chain.demand:= by
  obtain ⟨hp,hq⟩:= fresh h he; unfold weight
  have ht : e.1∉ insert e.2 (D.mouths C):=by simp [hp,(h.boundary e he).1]
  rw [h.benefit he,Finset.sum_insert ht,Finset.sum_insert hq]; dsimp [thread]; linarith [(C.budget e (h.isPair he)).2.2]

variable (hp:Gap S e D C)
local notation "L" => within S e D C
local notation "R" => within (D.lands \ S) e D C
include hp
lemma split_count : (L).weight C + (R).weight C=(D.less e).weight C -4:= by
  unfold weight; rw [← split_union h he hp,Finset.sum_union (h.split_disjoint he hp)]; ring
lemma split_chart : (L).opens C ∪ (R).opens C=(D.less e).opens C:=by unfold opens; rw [← split_union h he hp]; simp only [Chart.hands,Finset.union_biUnion]
lemma alignment : ((L).mouths C).erase e.1 ⊆ D.mouths C:= by
  have hv:e.2∈ (R).mouths C:= by
    rw [(mouth_regions h he hp).2,h.benefit he]; exact Finset.mem_filter.mpr ⟨by simp,Finset.mem_sdiff.mpr ⟨(pathV h he he).2,hp.no⟩⟩
  intro i hi; obtain ⟨hh,ha⟩:=Finset.mem_erase.mp hi
  have ht:i∈(D.less e).mouths C:= (split_union h he hp) ▸ Finset.mem_union_left _ ha
  rw [h.benefit he] at ht; have hk:i≠e.2:= fun hy=>Finset.disjoint_left.mp (split_disjoint h he hp) ha (hy.symm ▸ hv)
  simpa [hh,hk] using ht
end Clear
end District
end YM.MSbar.Pole.Feynman
