import YM.MSbar.Pole.Book.Canonical
/-! # Finite-rule ordinary-vertex normalization

Numerators in Fourier conventions. An `atom` is one dot expression with
real/complex coefficient; every ordinary-polynomial bare rule written in the
stable dot convention via finite linear combinations over these vertices.
Arbitrarily many slots in monomials; dummy vacuum terms are stripped.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Book
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {G:Gauge}
abbrev Dims {n : ℕ} (f:Fin n →Tag G):= Sigma fun i=>Fin (f i).rank
abbrev Alphabet {n : ℕ} (f:Fin n →Tag G):= (Fin n) ⊕ Dims f
scoped instance (priority:=high) {n : ℕ} (f : Fin n→Tag G) : BEq (Alphabet f) := instBEqOfDecidableEq
scoped instance (priority:=high) {n : ℕ}(f:Fin n→Tag G) : LawfulBEq (Alphabet f):= @instLawfulBEq (Alphabet f) _ -- find
-- keep field-vs-anchor momentum designation

structure Atom (G:Gauge) where
  length : ℕ+
  f : Fin length → Tag G
  gpower : ℕ
  c : ℂ
  L : Links (Alphabet f)
  reels : (∑ i, (f i).degree) + (( (tour L).filter Sum.isLeft).length:ℕ) = (4:ℤ)
  each : ∀ i : Dims f,(tour L).count (Sum.inr i)=1

namespace Installation
variable {V:Type} [Fintype V] [Nonempty V] (F : V → Atom G)

def panel : Profiles G V:=⟨fun v=> (F v).length,fun v=> (F v).f⟩
abbrev Code := (panel F).Axis
local instance (priority:=high): DecidableEq (Code F):= fun a b=> Classical.propDecidable (a=b)

def frames (v:V):Alphabet (F v).f → Code F := Sum.elim ((panel F).intrude v) fun q=> (panel F).flag v q.1 q.2
theorem proper (v:V): Injective (frames F v):=by
  rintro (i|⟨i,j⟩) (x|⟨x,y⟩) h <;> try contradiction
  · change Sum.inl ⟨v,i⟩= (Sum.inl ⟨v,x⟩:Code F) at h; simp only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] at h; rw [-- case args
  h]
  change Sum.inr ⟨⟨v,i⟩,j⟩=(Sum.inr ⟨⟨v,x⟩,y⟩:Code F) at h
  rcases Sigma.mk.inj (Sum.inr.inj h) with ⟨hi,hj⟩; cases heq_of_eq hi --
  grind

def pairs (v:V) := (F v).L.map (Prod.map (frames F v) (frames F v))
lemma traveled (v:V): tour (pairs F v)=(tour (F v).L).map (frames F v):=by
  unfold pairs; generalize (F v).L=L; induction L with
  | nil=> rfl
  | cons i l ih=>simpa [tour] using ih
lemma aged (v:V):
    let P:=panel F; (Leaf v).weight P.toChart = (-(amount (P.toChart.mom) (pairs F v):ℕ):ℤ):= by
  intro P; have hp : (Leaf v).mouths P.toChart= _:=P.unit v
  have hx : ∑ i∈(Leaf v).mouths P.toChart,P.toChart.age i=∑ i,((F v).f i).degree:= by
    rw [P.unit,Finset.sum_image]; exact rfl
    intro i _ j _ he
    have hj := proper F v (a₁:=Sum.inl i) (a₂:=Sum.inl j) he; exact Sum.inl.inj hj
  have hm : amount P.toChart.mom (pairs F v)= (((tour (F v).L).filter Sum.isLeft).length):= by
    rw [amount,traveled]; have he(x:Alphabet (F v).f): decide (frames F v x∈P.toChart.mom)= Sum.isLeft x:= by
      cases x with
      | inl x=> simp [frames,P,Profiles.intrude,Profiles.toChart,Profiles.legs]
      | inr x=> simp [frames,P,Profiles.flag,Profiles.eye,Profiles.toChart,Profiles.legs]
    generalize tour (F v).L=L; induction L with
    | nil=>rfl
    | cons x l ih=> simp only [List.map_cons,List.filter_cons]; -- match decide diffs
                    rw [he]; split <;> simp [ih]
  rw [hm,weight,hx]; linarith only [(F v).reels]

lemma vertices (v:V):
    let P:=panel F; let M:=P.toChart
    let H:Cloud (Code F):= fun n x=>links (pairs F v) n (Tip.anchor ((Leaf v).mouths M) (leader (Leaf v) M) x)
    Local M.mom ((Leaf v).weight M) H ∧ Shape ((Leaf v).view M) ((Leaf v).opens M) H := by
  intro P M H; have he:= (P.baseline v); let L:=pairs F v
  refine ⟨fixed_frame _ (by rw [aged F]; exact grades (I:=Code F) L _) ((Leaf v).borders M) he.chief,
     linear_at (R:=(Leaf v).mouths M) (F:=links L) ⟨?_,?_⟩ (Finset.disjoint_left.mpr fun i hi h=> Finset.disjoint_left.mp he.notations ((Leaf v).borders M h) hi) he.chief⟩
  · refine fun n x y hx=> detects L _ _ _ fun i hi=> hx i ?_
    have hh := List.mem_toFinset.mp hi
    rw [show L=pairs F v from rfl,traveled] at hh
    obtain ⟨u,-,hu⟩:= List.mem_map.mp hh
    subst i; cases u with
    | inl i=> apply Finset.mem_union_left; rw [P.unit]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    | inr i=> exact Finset.mem_union_right _ ((P.covers v _).mpr ⟨i.1,i.2,rfl⟩)
  intro i hi; obtain ⟨x,y,hq⟩:=(P.covers v _).mp hi; subst i
  apply bent; have hh:= (F v).each (⟨x,y⟩:Dims (F v).f); unfold L; rw [traveled];
  letI : BEq (Code F) := instBEqOfDecidableEq
  change List.count (frames F v (Sum.inr (⟨x,y⟩:Dims (F v).f))) (List.map _ _) = _
  rw [List.count_map_of_injective _ _ (proper F v)]; exact hh
def make : Menu (Code F) V where
  chart := (panel F).toChart
  vertex v :=
    let P:= panel F; let M:= P.toChart
    (F v).c • fun n (x:External (Code F) n)=>links (pairs F v) n (Tip.anchor ((Leaf v).mouths M) (leader (Leaf v) M) x)
  localAt v:= by have he:= vertices F v; exact ⟨he.1.number _, he.2.scale _⟩

end Installation
end YM.MSbar.Pole.Book
