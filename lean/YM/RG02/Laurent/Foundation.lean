import YM.RG02.Roots.Extent
import YM.Work.E01

/-!
Connect on a finite graph of factors (whole vertices, vacuum triangle
support including bases, Wick lines; confluent output slots). Use CORE
coarse mesh cover coordinates for every offset. Each factor has an anchor
among its slots. Winding can only occur when total relative length is enough
to go around this actual torus; even an isolated loop at a point with no
legs must be assigned a slot. Charges count open and closed orientations.
Handles arbitrary multiplicities. Include *all* positions of other roots.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG02.Laurent
open Function Equiv Lattice Finset Work Extra.Trajectories Marks
open scoped Classical BigOperators
variable {B V : Type}
variable [Fintype B]

-- max norm native, not physical regulator distance.
def stride (x:Cover) := Finset.univ.sup fun i : Axis => Int.natAbs (x i)
lemma stride_wrap (n:Side)(x:Cover) : pdist (wrap n x) ≤ stride x:= by
    apply Work.E01.pdist_wrap_le
    apply box_test.mpr; constructor <;> intro i
    · have h : Int.natAbs (x i) ≤ stride x:= le_sup (f:=fun j=>Int.natAbs (x j)) (mem_univ i); omega
    have h : Int.natAbs (x i) ≤ stride x:= le_sup (f:=fun j=>Int.natAbs (x j)) (mem_univ i); omega
lemma stride_neg (x:Cover): stride (-x)=stride x:= by simp [stride]
lemma stride_add (x y:Cover) : stride (x+y)≤stride x+stride y:= by
    apply Finset.sup_le; intro i _
    have hx : Int.natAbs (x i)≤ stride x:= le_sup (f:=fun j=>Int.natAbs (x j)) (mem_univ _)
    have hy : Int.natAbs (y i)≤ stride y:= le_sup (f:=fun j=>Int.natAbs (y j)) (mem_univ _)
    exact (Int.natAbs_add_le ..).trans (add_le_add hx hy)
lemma stride_sub (x y:Cover) : stride (x-y)≤stride x+stride y:= by rw [sub_eq_add_neg]; simpa only [stride_neg] using stride_add x (-y)
lemma returns {x:Cover}{n:Side}(h:2*stride x<n.val) : lift (wrap n x)=x:=by
    apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; have hx : Int.natAbs (x i)≤ stride x:= le_sup (f:=fun j=>Int.natAbs (x j)) (mem_univ _); omega
lemma equivariant {n:Side}(x:Site n) : stride (lift x)=pdist x:= rfl -- n implicit?

structure Ringlet (V B:Type) where
    set : V → Finset B
    base : ∀ i, ↑(set i)

namespace Ringlet
variable (L:Ringlet V B)
-- pinned d_k offsets before any support integration at THIS vertex
abbrev Relative (X:Type)(i:V)[Zero X]:= {t : (↑(L.set i))→X//t (L.base i)=0}

variable {G U : Type} [AddCommGroup G][AddCommGroup U]

def slice (t:B→G)(i:V) : Relative L G i:= ⟨fun j=> t j.val-t (L.base i).val, sub_self _⟩

def castAll (f:G→+U)(d : ∀ i,L.Relative G i)(i:V) : Relative L U i:= ⟨fun j=> f ((d i).val j), by dsimp only; rw [(d i).property,f.map_zero]⟩
def tensorLinked (i j:B) : Prop := ∃ k:V,i∈L.set k ∧ j∈L.set k
def Bridges := NoCut univ (tensorLinked L)
variable {L}

-- base-independent. Includes holonomies along cycles. NOT requiring
-- output projection to a fundamental domain.
def Balanced (d : ∀ i,L.Relative G i) : Prop := ∃ t:B→G,L.slice t=d
omit [Fintype B] in
lemma translatable {d : ∀ i,L.Relative G i}{z:B→ G} (he:L.slice z=d) (g:G) : L.slice (fun i=>z i + g)=d:=by
    funext i; subst d; apply Subtype.ext; funext j; exact add_sub_add_right_eq_sub ..

omit [Fintype B] in
lemma carried {d : ∀ i,L.Relative G i}{z:B→G}(h:L.slice z=d)(f:G→+U) : L.slice (f ∘ z)= L.castAll f d:=by
    rw [← h]; funext i; apply Subtype.ext; funext j; exact (f.map_sub ..).symm

lemma equal (he:L.Bridges){z w:B→G}(h:L.slice z=L.slice w){b:B}(hb:z b=w b) : z=w:=by
    let t:= univ.filter fun i:B=> z i=w i
    by_cases H:t=univ
    · exact funext fun i=> (mem_filter.mp (show i∈ t from H ▸ mem_univ i)).2
    obtain ⟨i,hi,j,hj,l,hh,hk⟩:= he t (subset_univ _) ⟨b,mem_filter.mpr ⟨mem_univ _,hb⟩⟩ (sdiff_nonempty.mpr (fun h=>H (Finset.Subset.antisymm (subset_univ _) h)))
    have hx : ∀ p: ↑(L.set l), z p.val-z (L.base l).val=w p.val-w (L.base l).val:= congr_fun (congr_arg Subtype.val (congr_fun h l))
    have ht := hx ⟨i,hh⟩; have hu:=hx ⟨j,hk⟩
    change z i-_=w i-_ at ht; rw [(mem_filter.mp hi).2,sub_right_inj] at ht
    change z j-_=w j-_ at hu; rw [ht,sub_left_inj] at hu
    exact False.elim ((mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ _,hu⟩))

variable (L)
def bulk (i:V)(d:Relative L Cover i) := ∑ j: ↑(L.set i),stride (d.val j)
variable {L}[Fintype V]

def Fuel (d : ∀ i,L.Relative Cover i) := ∑ i:V,L.bulk i (d i)

variable {n:Side}

omit [Fintype B] in
lemma component (u : ∀ i,L.Relative Cover i) (i:V)(j : ↑(L.set i)) : stride ((u i).val j)≤Fuel u:=by
    refine le_trans (b:=L.bulk i (u i)) ?_ (single_le_sum (f:=fun i=>L.bulk i (u i)) (fun k _=> Nat.zero_le _) (mem_univ i))
    exact single_le_sum (f:=fun j: ↑(L.set i)=> stride ((u i).val j)) (fun k _=> Nat.zero_le _) (mem_univ _)

lemma spans {u : ∀ i,L.Relative Cover i}{t:B→Site n} (he : Bridges L)(h:L.slice t=L.castAll (wrap n) u)(b i:B) :
    separation (t i) (t b)≤ Fintype.card B*(2*Fuel u):=by
    have Q(j:V)(x: ↑(L.set j)): t x.val - t (L.base j).val=wrap n ((u j).val x):= congr_fun (congr_arg Subtype.val (congr_fun h j)) _
    rw [← card_univ]
    apply Roots.extension _ _ _ he ?_ (mem_univ _) (mem_univ _)
    rintro i _ r _ ⟨k,hi,hh⟩
    refine (separation_triangle _ (t (L.base k).val) _).trans ?_
    rw [separation_comm (t (L.base k).val)] -- second
    unfold separation
    rw [Q k ⟨i,hi⟩,Q k ⟨r,hh⟩, two_mul]; exact add_le_add ((stride_wrap ..).trans (component u ..)) ((stride_wrap ..).trans (component u ..))

-- and even before projection to torus
lemma reach {u : ∀ i,L.Relative Cover i}{t:B→ Cover} (he : Bridges L)(h:L.slice t=u)(b i:B) :
    stride (t i-t b)≤ Fintype.card B*(2*Fuel u):=by
    let n:Side:=⟨2*stride (t i-t b)+1,by omega⟩
    have hh:=spans he (carried h (wrap n)) b i
    dsimp only [Function.comp_apply] at hh
    rwa [separation,← map_sub,← equivariant,returns (by unfold n; simp)] at hh

private lemma active (b:B) : 0<Fintype.card B:= @Fintype.card_pos B _ ⟨b⟩

lemma unwound {u : ∀ i,L.Relative Cover i} (b:B) (he : Bridges L)(h:Balanced (L.castAll (wrap n) u))
    (hv : 4* Fintype.card B * (2*Fuel u)< n.val) : Balanced u:=by
    obtain ⟨t,h⟩:= h
    let f (i:B):= lift (t i-t b)
    have hF i: stride (f i) ≤ Fintype.card B * (2*Fuel u):= spans he h b i
    refine ⟨f,funext fun i=> Subtype.ext (funext fun j=>?_)⟩
    change f j.val - f (L.base i).val= _
    have hq : 2*stride (f j.val-f (L.base i).val) < n.val:=by
       refine lt_of_le_of_lt (Nat.mul_le_mul_left 2 ((stride_sub ..).trans (add_le_add (hF _) (hF _)))) ?_
       suffices 2*(Fintype.card B*(2*Fuel u)+Fintype.card B*(2*Fuel u))=4*Fintype.card B*(2*Fuel u) from this.trans_lt hv; ring
    have ht : 2 * stride ((u i).val j)< n.val:=by
       have hw : Fuel u ≤ Fintype.card B*Fuel u:=Nat.le_mul_of_pos_left _ (active b)
       have hb:=component u i j; refine lt_of_le_of_lt ?_ hv; nlinarith only [hw,hb,Nat.zero_le (Fuel u)]
    rw [← returns hq,← returns ht]; apply congr_arg
    rw [map_sub]; unfold f; simp only [wrap_lift,sub_sub_sub_cancel_right]
    exact congr_fun (congr_arg Subtype.val (congr_fun h i)) j
end Ringlet
end YM.RG02.Laurent
