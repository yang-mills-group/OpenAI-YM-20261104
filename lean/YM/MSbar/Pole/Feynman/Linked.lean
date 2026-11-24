import YM.MSbar.Pole.Feynman.Attains
/-! # Evolution of whole connected diagrams -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman.District
open Set Function Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Piece
open scoped Topology ContDiff BigOperators Classical
variable {I V:Type} [Fintype I] [Nonempty I] {F:District I V} {e:I×I} {C:Chart I V}

def Exact (C:Chart I V) (F:District I V) (s:List (Piece I)) := Stack s C.mom (F.weight C) (F.view C) (F.opens C)
def Young (C:Chart I V) (F:District I V) (s:List (Piece I)):= Flag s C.mom (F.weight C) (F.view C) (F.opens C)

lemma herald {s :List (Piece I)} (h : F.Clear C) (he:e∈F.paths) (hs:Exact C (F.less e) s) {μ:ℝ} (hμ:0<μ):
    Young C F (s.map (leap (F.thread C e) μ)) := by
  let T:= F.thread C e; have hb:T.Fits (F.opens C):=h.permission he
  have hp := supply hb (T:=T) (A:=C.mom) ?_ (h.unmoored he) (s:=s) (b:=(F.less e).weight C) ?_ μ hμ
  · rw [show ((F.less e).weight C-2-T.chain.demand)=F.weight C from (h.counting he).symm] at hp; exact hp
  · rw [show T.inputs=_ from h.sameMark he]; exact borders ..
  rw [show T.inputs=_ from h.sameMark he,show T.chain.reads∪F.opens C=_ from h.corresponds he]
  apply Piece.Stack.raises hs _ (by rfl); exact Finset.union_subset_union (Finset.erase_subset _ _) (by rfl)

def minus (L:District I V)(C:Chart I V)(e:I×I):= (L.mouths C).erase e.1
def assembly (F:District I V) (e:I×I) (L:District I V) (C:Chart I V) (x y:List (Piece I)) := (mix x y).map (ramp (F.thread C e) (minus L C e))

lemma across {x y :List (Piece I)} (h : F.Clear C) (he:e∈F.paths) {G:Finset V} (hg:Gap G e F C) :
    let X:=within G e F C; let Y:= within (F.lands\G) e F C
    Exact C X x→ Exact C Y y → Young C F (assembly F e X C x y):=by
  intro X Y hx hy
  have hp:X.mouths C∪Y.mouths C=(F.less e).mouths C:=h.split_union he hg
  have hr:X.opens C∪Y.opens C=(F.less e).opens C:=h.split_chart he hg
  have ha:Disjoint (X.opens C) (Y.opens C):= C.hands_separate (borders X C) (borders Y C) (h.split_disjoint he hg)
  have ht:=h.content he hg
  have h₁ : Disjoint (X.opens C) (Y.view C):= Finset.disjoint_union_right.mpr ⟨ht.1.notations.symm.mono_right ((Finset.erase_subset _ _).trans (borders Y C)),ha⟩
  have h₂ : Disjoint (Y.opens C) (X.view C):= Finset.disjoint_union_right.mpr ⟨ht.2.notations.symm.mono_right ((Finset.erase_subset _ _).trans (borders X C)),ha.symm⟩
  have hv:= smash hx hy h₁ h₂
  rw [hr] at hv
  have hz:= h.permission he; let T:= F.thread C e; have hW:= piers (T:=T) hz (?_ : T.inputs⊆ C.mom) (h.unmoored he) (b:=X.weight C+Y.weight C) (s:=mix x y) ?_ (minus X C e) (h.alignment he hg)
  · have hf : X.weight C + Y.weight C +2-T.chain.demand=F.weight C:=by rw [show X.weight C + Y.weight C=_ from h.split_count he hg,h.counting he]; unfold T; ring
    rw [hf] at hW; exact hW
  · rw [show T.inputs=_ from h.sameMark he]; exact borders ..
  rw [show T.inputs=_ from h.sameMark he, show T.chain.reads∪F.opens C=_ from h.corresponds he]
  apply hv.raises _ (by rfl)
  rw [← hp,← hr];
  intro i hi; unfold view at hi; simp only [Finset.mem_union,Finset.mem_erase] at *; tauto

lemma one (h:F.Clear C) (hp:F.paths=∅): ∃ v:V,F.lands={v}:=by
  obtain ⟨v,hv⟩:=h.nonempty; refine ⟨v,((h.connected {v} (Finset.singleton_subset_iff.mpr hv) (fun x hh=>by rw [hp] at hh; simp at hh)).resolve_left (by simp)).symm⟩

/-- Vertex indexing and weights and numerator for any list of bare vertices. -/
def Leaf (v:V):District I V:= ⟨{v},∅⟩
end YM.MSbar.Pole.Feynman.District
