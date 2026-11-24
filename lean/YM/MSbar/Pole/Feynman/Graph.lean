import YM.MSbar.Pole.Sew.Garden
/-!
# Finite incidence graph for a directional/tensor amplitude

Momentum in D-space at a leg directed *into* its vertex. The partner call names ordered
pair `(left,right)`, with ±p, and is not made again on its reverse. Uses halfedges to
allow arbitrary self-contractions and parallel series. Distinct vertex names. `V` and
`I` need not be exhausted by one diagram (one may reserve the tables for the horizon).
Momentum conservation and solving for the canonical root part done before contraction.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman
open Function Set Filter MeasureTheory Momentum Ambient Symbol Piece Sew Thread
open scoped Topology ContDiff BigOperators Classical
variable {I V : Type}

/-- All options used by a class of contractions over these labeled halfedges.
Scalar convention value includes line normalization; diagram polarity besides the
oriented propagator signs computed afterwards. -/
structure Chart (I V : Type) where
  mom : Finset I -- all momentum slot names incl ghosts, sources and antifields
  eye : I → Finset I -- flags for tensor polarization use at this name
  age : I → ℤ -- mass dimension, sources have weight 4-d
  home : I → V -- vertex location
  pair : I × I → Prop
  chain : I × I → Chain I
  constant : I × I → ℂ
  -- licenses
  separate i : i∈mom → Disjoint (eye i) mom
  unique i j : i∈mom → j∈mom → i≠j → Disjoint (eye i) (eye j)
  budget (p : I × I) : pair p → (chain p).usable ∧ (chain p).reads = eye p.1 ∪ eye p.2 ∧ age p.1+age p.2= 2+(chain p).demand

/-- chart districts. Edges are named by ordered momenta. -/
structure District (I V : Type) where
  lands : Finset V
  paths : Finset (I × I)
namespace Chart
variable (C : Chart I V)
def venues (X : Finset V) := C.mom.filter fun i=> C.home i∈X
def hands (X : Finset I):= X.biUnion C.eye
@[simp] lemma appears (X : Finset V) (i : I) : i∈C.venues X↔ i∈C.mom∧ C.home i∈X:=by simp [venues]
end Chart
namespace District
variable (F : District I V)
def ends (S : Finset (I×I)) := S.biUnion fun x=> {x.1,x.2}
def mouths (C : Chart I V):= C.venues F.lands \ ends F.paths

def Crossing (C : Chart I V) := ∀ W : Finset V, W ⊆ F.lands →
     (∀ p ∈ F.paths, (C.home p.1∈W ↔ C.home p.2∈W)) → W=∅∨W=F.lands

structure Clear (C : Chart I V) : Prop where
  connected : F.Crossing C
  mouths : (F.mouths C).Nonempty
  boundary (p) : p∈F.paths→ p.1≠p.2 ∧ p.1∈C.venues F.lands ∧ p.2∈C.venues F.lands ∧ C.pair p
  unique (p q : I×I) : p∈F.paths→ q∈F.paths→p≠q→ Disjoint ({p.1,p.2}:Finset I) {q.1,q.2}

variable {F}
lemma Clear.nonempty {C : Chart I V} (h:F.Clear C) : F.lands.Nonempty:=by obtain ⟨i,hi⟩:=h.mouths; exact ⟨C.home i,((C.appears ..).1 (Finset.mem_sdiff.mp hi).1).2⟩
lemma Clear.isPair {C : Chart I V}(h:F.Clear C){e:I×I}(he:e∈F.paths) : C.pair e:= (h.boundary _ he).2.2.2

lemma Clear.excludes {C : Chart I V} (h:F.Clear C){p:I×I}(hx:p∈ F.paths) : p.1∉ ends (F.paths.erase p) ∧ p.2∉ ends (F.paths.erase p):= by
  have he (i : I) (hi : i∈({p.1,p.2}:Finset I)) : i∉ends (F.paths.erase p):= by
    intro hh; obtain ⟨q,hq,hg⟩:=Finset.mem_biUnion.mp hh; exact Finset.disjoint_left.mp (h.unique p q hx (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq).symm) hi hg
  exact ⟨he _ (by simp),he _ (by simp)⟩

def less (F:District I V)(e:I×I): District I V:= ⟨F.lands,F.paths.erase e⟩
-- omit to needy neighborhoods
lemma Clear.benefit {C:Chart I V}(h:F.Clear C){e:I×I}(he:e∈F.paths) :
    (F.less e).mouths C=insert e.1 (insert e.2 (F.mouths C)):=by
  obtain ⟨ha,hb⟩:= h.excludes he; obtain ⟨-,hl,ht,-⟩:=h.boundary e he
  have hp:= Finset.insert_erase he
  have hh : ends F.paths=({e.1,e.2}:Finset I)∪ends (F.paths.erase e):=by
    conv_lhs=> rw [← hp]
    simp only [ends,Finset.biUnion_insert]
  ext x; change (x∈C.venues F.lands \ ends (F.paths.erase e)) ↔ x ∈ insert e.1 (insert e.2 (C.venues F.lands \ ends F.paths)); by_cases hz:x=e.1
  · subst x; rw [Finset.mem_sdiff]; simp only [Finset.mem_insert, true_or, iff_true]; exact ⟨hl,ha⟩
  by_cases hy:x=e.2
  · subst x; rw [Finset.mem_sdiff]; simp only [Finset.mem_insert, true_or, or_true, iff_true]; exact ⟨ht,hb⟩
  simp only [Finset.mem_sdiff,Finset.mem_insert,hz,hy,hh,Finset.mem_union,Finset.mem_singleton,false_or]
lemma Clear.pauses {C:Chart I V} (h:F.Clear C) {p} (he:p∈F.paths)(hh:(F.less p).Crossing C) : (F.less p).Clear C := by
  refine ⟨hh,?_,fun i hi => h.boundary i (Finset.mem_of_mem_erase hi), fun i j hi hj hg=> h.unique i j (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj) hg⟩; rw [h.benefit he]; exact Finset.insert_nonempty ..
end District
end YM.MSbar.Pole.Feynman
