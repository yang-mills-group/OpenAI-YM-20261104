import YM.OPE.Backup.Untouched
/-! # Keep herbs: allow dormant unit to keep moving all the way on its true path -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V : Type} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}
variable {Y : Type} [Fintype Y][DecidableEq Y] {L : Fibers Y V}
namespace Salt
variable (Z:Salt V Y L G n)(t:ℝ){v:V}
local notation "K"=> Z.vessel t
include t
lemma aloneKiln {p:(Bud Y).Mode} {s:Support n}(he:p.val.image Z.grain ⊆ s)(ht:p.val ⊆ {L.twig v}): Z.kiln s p=s:=by
   apply union_eq_left.mpr; intro j hj; obtain ⟨i,hi,rfl⟩:=mem_image.mp hj; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; have hp:L.twig (L.bunch k)=k:=by rw [mem_singleton.mp (ht hk), L.sectioned]
   rw [Salt.focus,hp]; exact he (mem_image_of_mem Z.grain hk) -- cast
lemma quietAt (h: Z.Breeze t) (hv:L.Solo v)(hp:Z.pepper (L.twig v)=0)(U:Config G n): (K).QuietAt v U:=by
   refine ⟨fun i hi=> Z.aloneKiln t i.property.2 hi,fun i hi hx he=>?_⟩; obtain ⟨i,b⟩:=i
   change Z.bud t U _ ≠ 0 at hx; unfold bud at hx; split at hx
   next h1=>
    have hB:¬ Healthy t (Z.kiln (Z.leaf i) (Z.marker i)) U:=fun ha=> Bool.false_ne_true ((show b=false from he).symm.trans (h1.mp ha)) -- `he` equals b=false, not not
    rcases i with i|i
    · change Z.pepper i ≠ 0 at hx; apply hx; rw [show i=L.twig v from mem_singleton.mp (hi (mem_singleton_self _)),hp]
    change ¬ Healthy t (Z.kiln i.val.1 i.val.2) U at hB; rw [Z.aloneKiln t i.property.2 hi] at hB; exact hB ((h.home i.val.1).permits U (fun h1=> hx (show (Z.air _ U).part i.val.2=0 from by rw [h1]; rfl)))
   contradiction
lemma soil_preserves (h: Z.Breeze t) (hv:L.Solo v)(hp:Z.pepper (L.twig v)=0)(U:Config G n)(x:Box n): (Z.soil t x U).part ((Bud V).fire v)=(Z.river x U).part ((Bud Y).fire (L.twig v)):= (K).soberSolo t U (Z.wet _ h) hv (Z.quietAt t h hv hp U) x |>.trans (congr_arg (fun p:Poly (Bud Y)=> p.part _) (Z.fieldSpend t U h x))
end Salt
open Accent
namespace Deck
-- remove pepper on passage
variable {V I : Type}[Fintype V] [DecidableEq V] {B:Census V}
lemma eraseFire (i:V)(s:B.Mode) (j:B.Mode): Poly.merges (B.fire i) j s ↔ i∈s.val ∧ j.val=s.val.erase i := by
   constructor
   · rintro ⟨hp,hq⟩; have ht:= Finset.disjoint_singleton_left.mp hp; rw [← hq]; simp [Census.fire,singleton_union,erase_insert ht] -- hp simp
   rintro ⟨hq,h⟩; unfold Poly.merges; rw [h]; simp [Census.fire,hq,singleton_union]
-- explicit dependent erase of tag i
variable {Δ : Fibers I V}
def pebble (B: Census V) (x : B.Mode) (i:V) : B.Mode:= ⟨x.val.erase i,B.down x.property _ (erase_subset ..)⟩
lemma fires_mul (i:V)(z:ℂ)(p:Poly B)(x:B.Mode) : (Poly.send (B.fire i) z*p).part x=if i∈x.val then z*p.part (pebble B x i) else 0:=by
    simp_rw [Poly.part_mul,Poly.part_send]; rw [sum_eq_single (B.fire i)]; swap; · intro b _ hb; simp [hb]
    swap; · simp
    simp only [if_true]; simp_rw [eraseFire]; simp_rw [show ∀ j:B.Mode,j.val=x.val.erase i ↔ j=pebble B x i from fun j=> ⟨fun hp=>Subtype.ext hp,fun hp=>congr_arg Subtype.val hp⟩]
    by_cases he:i∈x.val <;>simp [he]
variable [Fintype I][DecidableEq I]
namespace Token
variable {v:V}(hv:Δ.Solo v)
include hv
lemma invoiced (z:ℂ)(p:Poly (Bud I)): Fibers.reap Δ ((Poly.send ((Bud I).fire (Δ.twig v)) z)*p) = Poly.send ((Bud V).fire v) z*Fibers.reap Δ p:=by
    ext i; change (Poly.send ((Bud I).fire _) z*p).part (Δ.plena i)=_; simp only [fires_mul,reaped,Δ.sectioned v]; split; next he=>
       have hh : pebble _ (Δ.plena i) (Δ.twig v) = Δ.plena (pebble _ i v):=by
          apply Subtype.ext; ext b; rw [pebble,reaped]; change _ ↔ Δ.bunch b∈ i.val.erase v; rw [mem_erase,mem_erase,reaped]; exact and_congr_left fun hi=> not_congr ⟨fun hp=> hp ▸ Δ.sectioned _,fun hq=>(hv b hq).symm⟩ -- `pebble` rewrite both?
       rw [hh]; rfl
    rfl
omit hv
lemma several (f:V→ℂ)(s:Finset V)(h:∀ i∈s,Δ.Solo i) (p:Poly (Bud I)):
    Fibers.reap Δ ((∏ i∈s,(1+ Poly.send ((Bud I).fire (Δ.twig i)) (f i)))*p) =(∏ i∈s,(1+ Poly.send ((Bud V).fire i) (f i)))*Fibers.reap Δ p :=by induction s using Finset.induction_on with
     | empty=> simp
     | @insert i s hi IH=> rw [prod_insert hi,prod_insert hi,mul_assoc,mul_assoc,add_mul,map_add,invoiced (h _ (mem_insert_self ..)),one_mul,IH (fun i hi=>h i (mem_insert_of_mem hi)),add_mul,one_mul]
lemma passengers (u:I→ℂ)(s:Finset V)(h:∀ i∈s,Δ.Solo i) (p:Poly (Bud I)):
    Fibers.reap Δ (Poly.pass (Mach (Bud I) (fun i=>if Δ.bunch i∈s then u i else 0))*p)=Poly.pass (Mach (Bud V) (fun i=>if i∈s then u (Δ.twig i) else 0))*Fibers.reap Δ p:=by
    unfold Mach; rw [show (∑ i:I,Poly.send ((Bud I).fire i) (if Δ.bunch i∈s then u i else 0))= ∑ i∈s,Poly.send ((Bud I).fire (Δ.twig i)) (u (Δ.twig i)) from ?_]; swap
    · trans ∑ i ∈ (s.image Δ.twig),Poly.send ((Bud I).fire i) (u i)
      · rw [show (s.image Δ.twig)= univ.filter fun i=>Δ.bunch i∈s from ?_, Finset.sum_filter]; swap; · ext i; simp only [mem_image,mem_filter,mem_univ,true_and]; exact ⟨fun ⟨j,hj,hx⟩=>(show Δ.bunch i=j from hx ▸ Δ.sectioned j) ▸ hj,fun ht=>⟨Δ.bunch i,ht,h (Δ.bunch i) ht i rfl⟩⟩
        refine sum_congr rfl fun i _=>?_ ; split_ifs ; rfl; simp
      rw [sum_image (fun _ _ _ _ h=> Δ.sectioned.injective h)] -- sectioned LeftInverse bunch twig ok
    rw [show (∑ i:V,Poly.send ((Bud V).fire i) (if i∈s then u (Δ.twig i) else 0))=∑ i∈s,Poly.send ((Bud V).fire i) (u (Δ.twig i)) from ?_]; swap
    · simp_rw [show ∀ i:V, Poly.send ((Bud V).fire i) (if i∈s then u (Δ.twig i) else 0)=(if i∈s then Poly.send ((Bud V).fire i) (u (Δ.twig i)) else Poly.send ((Bud V).fire i) 0) from fun i=>apply_ite (Poly.send ((Bud V).fire i)) _ _ _,Poly.send_zero,← Finset.sum_filter]; simp
    rw [pass_sum s (fun i=>(Bud I).fire (Δ.twig i)) (by simp [Census.fire]),pass_sum s (Bud V).fire (by simp [Census.fire])]; exact several (u ∘ Δ.twig) s h _
end Token
end Deck
end YM.MergeProof.Ribbons.Fibers
