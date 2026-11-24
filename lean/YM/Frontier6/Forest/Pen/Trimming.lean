import YM.Frontier6.Forest.Pen.Charge

/-! The pruning step: maintain potential readings of all the external words at
 valuation strictly less than the band's value, with newly approximated projected
 alternatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
structure Top (K:Final C H S)(T:Fareway I)(L L':Finset ℝ)(r:ℝ):Prop where
   here : r ∈ L
   apex : ∀ a∈L, 0 ≤ a ∧ a ≤ r
   smaller : ∀ a∈L, a<r→ a∈L'
   routed : 0<r → Credit K T L'

def Prune (K:Final C H S)(T:Fareway I)(L':Finset ℝ)(r:ℝ)(a:ℝ)(P:Fabric I)(w:ℝ)(A:Art S I): Prop:= ∃ A':ℕ→Art S I, Prism K T r P A A'∧∀ᶠ i in atTop, Pen K T L' a P (A' i) w
structure Face (K:Final C H S)(T:Fareway I)(L':Finset ℝ)(r:ℝ)(a:ℝ)(P:Fabric I)(w:ℝ)(A:Art S I) : Prop where
    outer : a < r→ Prune K T L' r a P w A
    private_ : a = r→ Mist T r P A w
variable {T: Fareway I} {K:Final C H S}{L L':Finset ℝ}{P Q:Fabric I}{A B:Art S I}{w a u b r:ℝ}
namespace Face
variable (h:Face K T L' r a P w A)
include h
lemma cf (he:A=ᶠ[T.via] B): Face K T L' r a P w B:=by
   refine ⟨fun ha=> ?_,fun ha=> (h.private_ ha).cf he⟩; obtain ⟨v,hv,hQ⟩:=h.outer ha; exact ⟨v,hv.cf he (Eventually.of_forall fun _=> Filter.EventuallyEq.rfl),hQ⟩
lemma broader(he:Extends T Q P): Face K T L' r a Q w A:= by
   refine ⟨fun ha=> ?_,fun ha=>(h.private_ ha).weaker he⟩; obtain ⟨v,hv,hQ⟩:= h.outer ha; exact ⟨v,hv.broad he,hQ.mono fun _ hi=> hi.weaker he⟩
lemma mono (he:w≤u):Face K T L' r a P u A:=by
   refine ⟨fun ha=> ?_,fun ha=> (h.private_ ha).mono he⟩; obtain ⟨v,hv,hQ⟩:=h.outer ha; exact ⟨v,hv,hQ.mono fun _ hi=> hi.mono he⟩
lemma add (he:Face K T L' r a P w B): Face K T L' r a P w (A+B):=by
   refine ⟨fun ha=> ?_,fun ha=> (h.private_ ha).add (he.private_ ha)⟩; obtain ⟨v,hv,hQ⟩:=h.outer ha; obtain ⟨u,hu,hM⟩:=he.outer ha; exact ⟨v+u,hv.add hu,(hQ.and hM).mono fun _ hi=> hi.1.add hi.2⟩
lemma scale {c:I→ℂ}(he:T.Costs c u): Face K T L' r a P (u+w) (fun i=> c i • A i):=by
   refine ⟨fun ha=> ?_,fun ha=> (h.private_ ha).scale he⟩; obtain ⟨v,hv,hQ⟩:=h.outer ha; exact ⟨fun d i=> c i • v d i,hv.scale (Bicolor.rfl he), hQ.mono fun _ hi=> hi.scale he⟩
lemma mul (he:Face K T L' r a Q u B) (hp: Cross T P Q a): Face K T L' r a (P⊔Q) (w+u) (A*B):=by
   refine ⟨fun ha=> ?_,fun ha=> (h.private_ ha).multiplication (he.private_ ha) (ha ▸ hp)⟩; obtain ⟨v,hv,hQ⟩:=h.outer ha; obtain ⟨u',hu,hM⟩:=he.outer ha; exact ⟨v*u', hv.mul hu hp ha,(hQ.and hM).mono fun _ hi=> hi.1.mul hi.2 hp⟩
omit h
lemma tip {x:I→ E4} (he: Contains T P x)(v:S.Tag):Face K T L' r a P (v.fst*a) (fun i=>letter S (x i) v):=by
   refine ⟨fun _=> ⟨_,Prism.step v he,Eventually.of_forall fun _=>Pen.tip he v⟩, fun h=> ?_⟩; rw [h]; exact Mist.step v he
lemma zero : Face K T L' r a P w 0:= ⟨fun _=> ⟨_,Prism.zero, Eventually.of_forall fun _=> Pen.zero⟩, fun _=> Mist.zero _⟩
end Face
end YM.Frontier6.Forest
