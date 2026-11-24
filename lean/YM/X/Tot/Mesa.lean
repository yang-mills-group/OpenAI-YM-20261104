import YM.X.Tot.Meter
/-!
# Geometry exists (actual deployment(s)) and preserves tally. Useful cast-free.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ}
local notation "fℕ"=>(atTop:Filter ℕ)
variable (q:ℕ+)(x y z:Fielding.Walk) (χ:Floor R)
def Clear (q:ℕ+)(r:ℝ)(x y:Fielding.Walk):Prop:= ∃ a b, plot q x a∧ plot q y b∧ r<‖a-b‖
def Geom (q:ℕ+)(r:ℝ)(x y z:Fielding.Walk):Prop:= Clear q r x y∧ Clear q r y z ∧ Clear q r z x
lemma Clear.sym (h:Clear q r x y):Clear q r y x:= by obtain ⟨a,b,h,h',hr⟩:=h; exact ⟨b,a,h',h,norm_sub_rev b a ▸ hr⟩ -- orientation check
namespace Geom
lemma circles(h:Geom q r x y z):Geom q r y z x:= ⟨h.2.1,h.2.2,h.1⟩
lemma swap(h:Geom q r x y z):Geom q r x z y:= ⟨Clear.sym q _ _ h.2.2,Clear.sym q _ _ h.2.1,Clear.sym q _ _ h.1⟩
abbrev head (x y z:Fielding.Walk): Fin 3→Fielding.Walk:= ![x,y,z]
variable (h:Geom q r x y z)
include h
lemma reach : ∃ a:Fin 3→E4, Apart Finset.univ a r∧ ∀ i,plot q (head x y z i) (a i):= by
    obtain ⟨⟨a,b,ha,hb,ht⟩,⟨b',c,h,hc,hw⟩,⟨c',a',hl,hh,hv⟩⟩:=h; rw [show c'=c from tendsto_nhds_unique hl hc, show a'=a from tendsto_nhds_unique hh ha] at hv; rw [show b'=b from tendsto_nhds_unique h hb] at hw
    refine ⟨![a,b,c],fun i _ j _ h=> ?_ ,fun i=>?_⟩; swap; · fin_cases i <;> first|exact ha|exact hb|exact hc
    have ha':= norm_sub_rev a c; have hb':= norm_sub_rev b a; have hc':= norm_sub_rev c b; fin_cases i<;>fin_cases j <;> simp_all -- h coerces equal
end Geom
local notation "F"=> Fin 3
local notation "W"=> List (Marks G × Tops G)
local notation "U"=> Finset.univ (α:=Fin 3)
variable (h:Geom q r x y z)(hq:1<q.val)(hr:R<r)
include h hq hr
lemma three_roof: usable (G:=G) q x y z (1-bend q χ x) 3 0 0:= by
    obtain ⟨f,h',hf⟩:= Geom.reach q x y z h; let a:=Geom.head x y z; rintro p b c hp hb hc; obtain rfl:b=[]:=List.eq_nil_of_length_eq_zero hb; obtain rfl:c=[]:=List.eq_nil_of_length_eq_zero hc; -- list unpack core
    have hP:∃ t u v,p=[t,u,v]:= List.length_eq_three.mp hp; obtain ⟨l,m,n,hP⟩:=hP; subst p; rw [arrows0,arrows0, mul_one,mul_one,arrows_next,arrows_next,arrows_next,arrows0,mul_one]; rw [show 1-bend q χ x= shore q χ {0} a from ?_]; swap; · rw [shore,Finset.sum_singleton];rfl
    rw [← mul_assoc (wire q x l.1 l.2) (wire q x m.1 m.2)]; apply most χ U a f h' hr (fun i _=>hf i) hq l.1 m.1 n.1 l.2 m.2 n.2 (hi:=Finset.mem_univ 0) (hj:=Finset.mem_univ 0) (hk:=Finset.mem_univ 0) {0} (Finset.subset_univ _); intro d hd; have ht:d≠0:=by simpa using hd
    simp [atMost,ht]
lemma two_roof : usable (G:=G) q x y z (1-bend q χ x) 2 1 0:= by
    obtain ⟨f,h',hf⟩:= Geom.reach q x y z h; let a:=Geom.head x y z; rintro p b c hp hb hc; obtain rfl:c=[]:=List.eq_nil_of_length_eq_zero hc; obtain ⟨l,m,rfl⟩:= List.length_eq_two.mp hp; obtain ⟨v,rfl⟩:= List.length_eq_one_iff.mp hb;
    rw [arrows0,mul_one,arrows_next,arrows_next,arrows0,mul_one,arrows_next,arrows0,mul_one]; rw [mul_assoc (1-_)];rw [show 1-bend q χ x= shore q χ {0} a from ?_]; swap; · rw [shore,Finset.sum_singleton]; rfl
    apply most χ U a f h' hr (fun i _=>hf i) hq l.1 m.1 v.1 l.2 m.2 v.2 (hi:=Finset.mem_univ 0) (hj:=Finset.mem_univ 0) (hk:=Finset.mem_univ 1) {0} (Finset.subset_univ _); intro d hd; have ht:d≠0:=by simpa using hd
    simp [atMost,ht]
lemma two_roof' : usable (G:=G) q x y z (1-bend q χ x) 2 0 1:= by intro a b c ha hb hc; have he:= two_roof q x z y χ (h.swap q ..) hq hr a c b ha hc hb; rwa [mul_right_comm] at he
include χ
lemma distinct_cost : usable (G:=G) q x y z 1 1 1 1 := by
    obtain ⟨f,h',hf⟩:= Geom.reach q x y z h; let a:=Geom.head x y z; intro p b c hp hb hc; obtain ⟨p,rfl⟩:= List.length_eq_one_iff.mp hp; obtain ⟨b,rfl⟩:= List.length_eq_one_iff.mp hb; obtain ⟨c,rfl⟩:= List.length_eq_one_iff.mp hc; rw [arrows_next,arrows0,mul_one,arrows_next,arrows0,mul_one,arrows_next,arrows0,mul_one]; rw [one_mul]; have hz:= most χ U a f h' hr (fun i _=>hf i) hq p.1 b.1 c.1 p.2 b.2 c.2 (hi:=Finset.mem_univ 0) (hj:=Finset.mem_univ 1) (hk:=Finset.mem_univ 2) ∅ (Finset.empty_subset _) (fun i _=>?_); simpa [shore,a,Geom.head] using! hz; unfold atMost; fin_cases i <;> simp
end YM.PositionX.Tot
