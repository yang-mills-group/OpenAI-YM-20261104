import YM.MSbar.Pole.Book.Material
/-! # Compatible presentation of a collection of d-dimensional integration vertices

One distinct label for each potential/ghost/auxiliary, antifield or mark factor.
Partition by vertex. Global linear axes carried outside vertex ordering. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Book
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {G:Gauge}
/-- finite fields and their types. -/
structure Profiles (G:Gauge)(V:Type) where
  leg : V → ℕ+
  sign : ∀ v,Fin (leg v)→Tag G
namespace Profiles
variable {V:Type} (p:Profiles G V) [Fintype V] [Nonempty V]
abbrev Leg := Sigma fun v=> Fin (p.leg v)
instance : Fintype p.Leg := by dsimp [Leg]; infer_instance
instance (v:V): NeZero (p.leg v).val := ⟨(p.leg v).pos.ne'⟩
instance : Nonempty p.Leg := by let i : V:=Classical.arbitrary _; exact ⟨⟨i,0⟩⟩
def kind (y:p.Leg) := p.sign y.1 y.2
abbrev Flag := Sigma fun x:p.Leg=> Fin (p.kind x).rank
instance : Fintype p.Flag := by dsimp [Flag]; infer_instance
abbrev Axis := p.Leg ⊕ p.Flag
local instance (priority := high) : DecidableEq p.Axis:=fun a b=>Classical.propDecidable (a=b)

def legs : Finset p.Axis := Finset.univ.image Sum.inl

def eye (x:p.Leg) (y:Fin (p.kind x).rank): p.Axis:= Sum.inr ⟨x,y⟩
def rays : p.Axis → Finset p.Axis | Sum.inl x=> Finset.univ.image (p.eye x) | _=> ∅
def lines (v : p.Axis × p.Axis) : Option (Chain p.Axis × ℂ) :=
  match v.1,v.2 with
  | Sum.inl x, Sum.inl y => if x=y then none else
                                      (p.kind x).line (p.kind y) (p.eye x) (p.eye y)
  | _,_=> none
lemma obeys (e:p.Axis × p.Axis) (i:Chain p.Axis × ℂ)(he : p.lines e=some i) :
    i.1.usable∧i.1.reads=p.rays e.1 ∪ p.rays e.2 ∧ ((Sum.elim (fun x=> (p.kind x).degree) (fun _=>0) e.1 + Sum.elim (fun x=> (p.kind x).degree) (fun _=>0) e.2)=2+(i.1.demand:ℤ)):=by
  rcases e with ⟨x | f,y | g⟩ <;> try contradiction
  change (if x=y then none else Tag.line _ _ _ _)=_ at he
  split_ifs at he with hh <;> try contradiction
  exact Tag.uses (fun i j=> by change p.eye x i ≠ p.eye y j; simp [eye,hh]) he

def onPair (x : p.Axis × p.Axis) := (p.lines x).getD (.scalar,0)
def toChart : Chart p.Axis V where
  mom := p.legs
  eye := p.rays
  age := Sum.elim (fun x=> (p.kind x).degree) (fun _=> 0)
  home := Sum.elim Sigma.fst (fun z=>z.1.1)
  pair v := (p.lines v).isSome
  chain v := (p.onPair v).1
  constant v := (p.onPair v).2
  separate i hi := by
    obtain ⟨x,-,hx⟩:=Finset.mem_image.mp hi; subst i
    apply Finset.disjoint_left.mpr; rintro _ ha hw; obtain ⟨k,-,rfl⟩:=Finset.mem_image.mp ha; obtain ⟨l,-,h⟩:=Finset.mem_image.mp hw; contradiction
  unique i j hi hj he := by
    obtain ⟨x,-,hx⟩:= Finset.mem_image.mp hi; obtain ⟨y,-,hy⟩:=Finset.mem_image.mp hj; subst i j
    apply Finset.disjoint_left.mpr; rintro _ ha hw; obtain ⟨k,-,rfl⟩:=Finset.mem_image.mp ha; obtain ⟨l,-,h⟩:=Finset.mem_image.mp hw; exact he (congr_arg _ (congr_arg Sigma.fst (Sum.inr.inj h)).symm)
  budget v hv:=by obtain ⟨i,he⟩:=Option.isSome_iff_exists.mp hv; unfold onPair; rw [he,Option.getD_some]; exact p.obeys v i he


def intrude (v:V) (i: Fin (p.leg v)):p.Axis:= Sum.inl ⟨v,i⟩
def flag (v:V)(i:Fin (p.leg v))(j:Fin (p.sign v i).rank):p.Axis:=p.eye ⟨v,i⟩ j
lemma unit (v:V):(Leaf v).mouths p.toChart = Finset.univ.image (p.intrude v):=by
  unfold Leaf mouths Chart.venues ends; ext x
  cases x with
  | inl z=>
    rcases z with ⟨w,j⟩; simp only [intrude,legs,toChart,Sum.elim_inl,Finset.biUnion_empty,Finset.sdiff_empty,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton,Sigma.mk.injEq,Sum.inl.injEq]
    constructor
    · rintro ⟨_,rfl⟩; exact ⟨j,rfl,HEq.rfl⟩
    rintro ⟨i,hp,hq⟩; exact ⟨⟨⟨_,_⟩,rfl⟩,hp.symm⟩
  | inr z=> simp [intrude,legs,toChart]
lemma covers (v:V)(x:p.Axis): x∈(Leaf v).opens p.toChart ↔ ∃ i j,x=p.flag v i j:=by
  unfold opens Chart.hands; rw [p.unit]; constructor
  · intro hx; obtain ⟨i,hi,hh⟩:=Finset.mem_biUnion.mp hx; obtain ⟨i,-,rfl⟩:=Finset.mem_image.mp hi; obtain ⟨j,-,rfl⟩:=Finset.mem_image.mp hh; exact ⟨i,j,rfl⟩
  rintro ⟨i,j,rfl⟩; exact Finset.mem_biUnion.mpr ⟨p.intrude v i,Finset.mem_image_of_mem _ (Finset.mem_univ i), Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
lemma baseline (v:V): Clear (Leaf v) p.toChart:=by
  constructor
  · intro W h _; by_cases hv:v∈ W
    · exact Or.inr (Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr hv))
    left; exact Finset.eq_empty_of_forall_notMem fun x hx=>hv ((Finset.mem_singleton.mp (h hx)) ▸ hx)
  · rw [p.unit]; exact Finset.image_nonempty.mpr ⟨0,Finset.mem_univ _⟩
  · intro x hp; simp [Leaf] at hp
  intro x _ hp; simp [Leaf] at hp
end Profiles
end YM.MSbar.Pole.Book
