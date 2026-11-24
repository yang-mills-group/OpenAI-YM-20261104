import YM.Frontier6.Forest.Tents.Clocks

/-!
# Footprints following a tariff

Separated **sets** of admissible live points. Projection cuts may change the
footprint globally, not the continuation positions used by the *other* trees.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{T:Fareway I}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book} (K:Final C H S)
abbrev Fabric (I:Type):= I→ Set E4
def Contains (T:Fareway I)(P:Fabric I)(x:I→ E4):Prop:=∀ᶠ i in T.via,x i ∈ P i
def Extends (T:Fareway I)(P Q:Fabric I):Prop:=∀ᶠ i in T.via,Q i ⊆ P i
def Cross (T:Fareway I)(P Q:Fabric I)(b:ℝ):Prop:=∀ a:ℝ,b<a→∀ᶠ i in T.via,∀ x∈P i,∀ y∈Q i,Real.exp (T.scale i*(-a)) ≤ ‖x-y‖
def Local (T:Fareway I)(P:Fabric I)(c:I→ E4)(b:ℝ):Prop:=∀ a:ℝ,a<b→∀ᶠ i in T.via,∀ x∈P i, ‖x-c i‖ ≤ Real.exp (T.scale i*(-a))
def Centered(T:Fareway I)(P:Fabric I)(c:I→ E4)(K: Final C H S)(d:ℕ):Prop:= ∃ r:ℝ, Frontier6.Safe K d (2*r)∧0<r∧∀ᶠ i in T.via,∀ x ∈ P i,‖x-c i‖≤r
variable {P Q Q' P':Fabric I}{b a:ℝ}{x y:I→ E4}
lemma Cross.symm (h:Cross T P Q b): Cross T Q P b:=fun a ha=>(h a ha).mono fun i hi x hx y hy=> (hi y hy x hx).trans_eq (norm_sub_rev ..)
lemma Cross.disjoint (h:Cross T P Q b):∀ᶠ i in T.via,Disjoint (P i) (Q i):= (h (b+1) (lt_add_one _)).mono fun i hi=> Set.disjoint_left.mpr fun {x} hx hy=> (not_le.mpr (Real.exp_pos _)) (by simpa only [sub_self,norm_zero] using hi x hx x hy)
lemma Cross.wide (h:Cross T P Q b)(hx:Contains T P x)(hy:Contains T Q y): ReachWide T x y b:= fun a ha=> ((hx.and hy).and (h a ha)).mono fun i hi=>hi.2 (x i) hi.1.1 (y i) hi.1.2
lemma Cross.mono (h:Cross T P Q b)(he:Extends T P P')(hv:Extends T Q Q') : Cross T P' Q' b := fun a ha=> ((he.and hv).and (h a ha)).mono fun i hi x hx y hy=> hi.2 x (hi.1.1 hx) y (hi.1.2 hy)
lemma Cross.scale (h:Cross T P Q b)(hp:b≤a): Cross T P Q a:= fun c hc=> h c (hp.trans_lt hc)
lemma Extends.rfl (P:Fabric I):Extends T P P:=Eventually.of_forall fun _=>Subset.rfl
lemma Extends.trans (h:Extends T P Q)(he:Extends T Q Q'):Extends T P Q':= (h.and he).mono fun _ hi=> Set.Subset.trans hi.2 hi.1
lemma Extends.contains (h:Extends T P Q)(he:Contains T Q x): Contains T P x:= (h.and he).mono fun _ hi=> hi.1 hi.2
lemma extends_left : Extends T (P⊔Q) P:= Eventually.of_forall fun i=>subset_union_left
lemma extends_right : Extends T (P⊔Q) Q:= Eventually.of_forall fun _=>subset_union_right
lemma Local.cost (h:Local T P y b)(he: Contains T P x): T.Costs (fun i=>x i - y i) (-b):= by intro a ha;filter_upwards [h (-a) (by linarith), he] with i hi he; simpa only [neg_neg] using hi _ he
lemma Local.ready (h:Local T P x b)(hp:0<b)(d:ℕ):Centered T P x K d:=by
    obtain ⟨r,hr,hQ⟩:= Frontier6.Safe.limits K d; have hx:= half_pos hr; have hy:=half_pos hp; refine ⟨r/2,?_,hx,?_⟩
    · convert hQ using 1; ring
    filter_upwards [(T.minted (-(b/2))).cheaper (T.minted_c _ hx) (neg_lt_zero.mpr hy), h (b/2) (half_lt_self hp)] with i hi hh y hy; exact (hh _ hy).trans hi.le
lemma Local.shrinks (h:Local T P x b)(he:Extends T P Q): Local T Q x b:=fun a ha=> ((h a ha).and he).mono fun i hi y hy=> hi.1 y (hi.2 hy)
lemma Centered.shrinks {d:ℕ}(h:Centered T P x K d)(he:Extends T P Q):Centered T Q x K d:=by
    obtain ⟨r,hr,hp,h⟩:= h; exact ⟨r,hr,hp,(he.and h).mono fun i hi y hy=> hi.2 y (hi.1 hy)⟩
def sheet (x:I→ V→ E4): Fabric I:= fun i=> Set.range (x i)
def thin (x:I→ E4) : Fabric I:= fun i=>{x i}
lemma Contains.self : Contains T (thin x) x:=Eventually.of_forall fun i=>rfl
lemma Contains.extends (h: Contains T P x): Extends T P (thin x):= h.mono fun i hi=> singleton_subset_iff.mpr hi
lemma Cross.thins (h:ReachWide T x y b): Cross T (thin x) (thin y) b:= fun a ha=>(h a ha).mono fun i hi x hx y hy=>by rwa [mem_singleton_iff.mp hx,mem_singleton_iff.mp hy]
lemma contains_sheet (x:I→ V→ E4)(i:V): Contains T (sheet x) (fun k=>x k i):= Eventually.of_forall fun _=>⟨i,rfl⟩
lemma extends_sheet [Finite V]{x:I→ V→ E4}(h:∀ v,Contains T P (fun i=> x i v)): Extends T P (sheet x):= (eventually_all.mpr h).mono fun i hi y ⟨k,hk⟩=> hk ▸ hi k
lemma unity {x:I→ V→ E4}{y:I→ X→ E4}(hx:Wide T x b)(hy:Wide T y b)(h:∀ i:V,∀ j:X,ReachWide T (fun k=>x k i) (fun k=>y k j) b): Wide T (fun i=>Sum.elim (x i) (y i)) b:=by
    rintro (i|i) (j|j) hi
    exacts [hx (fun hj=> hi (congr_arg Sum.inl hj)), h i j, (h j i).flip, hy (fun hj=> hi (congr_arg Sum.inr hj))]
lemma separate_range {x:I→ V→ E4}{y:I→ X→ E4}(h:Cross T (sheet x) (sheet y) b)(i:V)(j:X): ReachWide T (fun k=>x k i) (fun k=>y k j) b:= h.wide (contains_sheet x i) (contains_sheet y j)
end YM.Frontier6.Forest
