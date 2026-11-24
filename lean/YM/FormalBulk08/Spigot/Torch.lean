import YM.FormalBulk08.Spigot.Logic
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius
variable {o:Loc G 1}{l:ℕ}
variable {Y Z:Anthem D G}
lemma Glyph.sub (h:Glyph o Y l E)(hp:Glyph o Z l E): Glyph o (Y-Z) l E:= by
   refine ⟨⟨fun p a=> ?_,fun p a=>?_⟩, h.summary.sub hp.summary,fun n p=>?_⟩
   · simp_rw [Pi.sub_apply,h.map_add,hp.map_add]; abel
   · simp_rw [Pi.sub_apply,h.map_smul,hp.map_smul,smul_sub]
   have he:Kemp.banner l ((Y-Z) p) n=Kemp.banner l (Y p) n-Kemp.banner l (Z p) n:= by
       ext1 e; rw [map_sub]; simp_rw [Kemp.banner,coeff_mk]; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _=> (congr_arg (facade r) (sieve_sub_add n (h.summary.summable p e r) (hp.summary.summable p e r)).2).trans (map_sub ..)
   intro I i a b k ha hB ht hT hk hq he'; rw [he,map_sub,map_sub]; exact (h.glows n p I a b k ha hB ht hT hk hq he').sub (hp.glows n p I a b k ha hB ht hT hk hq he')
lemma wood_mono (h:Woodsy o σ A E Y)(hp:η ≤ σ)(hx:A≤ B): Woodsy o η B E Y:= ⟨h.height.trans hx,fun i hi r p=> (penn_shrink (h.precincts i hi r p) hp).mono (mul_le_mul_of_nonneg_right hx (norm_nonneg _))⟩
lemma wood_le (h:Woodsy o σ A E Y)(hp:Woodsy o σ B E Z): Woodsy o σ (A+B) E (Y-Z):= ⟨add_nonneg h.height hp.height,fun i hi r p=>by rw [add_mul]; exact penn_sub (h.precincts i hi r p) (hp.precincts i hi r p)⟩
lemma wood_plus (h:Woodsy o σ A E Y)(hp:Woodsy o σ B E Z): Woodsy o σ (A+B) E (Y+Z):= ⟨add_nonneg h.height hp.height,fun i hi r p=>by rw [add_mul]; exact (h.precincts i hi r p).add (hp.precincts i hi r p)⟩
lemma wood_zero (h:0≤A):Woodsy o σ A E (0:Anthem D G):=⟨h,fun _ _ _ _=> (Knox_zeros _).mono (mul_nonneg h (norm_nonneg _))⟩
-- stencil obligations for every label through q
structure Path (D:ℕ)(G:Gauge) where
    rank : ℕ
    grade : ℕ
    I : Type
    cabin : Cabin D I G rank
structure Merit (Q:Herald)(o:Loc G 1)(p:Path D G)(l u E:ℕ)(σ B:ℝ):Prop where
    alive : p.grade≤ E
    meets : p.rank≤ l+p.grade
    income: Energy p.cabin u σ B
    set:∀ i x,∃ v,(p.cabin.atoms i).leg x=Q.path v
    costs: Woodsy o σ B E (struck p.cabin p.grade)
variable (P:Dill) {Q:Herald}
lemma Merit.increase {a:Path D G} (h:Merit Q o a l u E σ A)(he:η≤σ)(hv:A≤ B): Merit Q o a l u E η B:= { h with income:=h.income.shrink he hv, costs:=wood_mono h.costs he hv }
include P
lemma sow_slot (Q:Herald) (o:Loc G 1)(r e:ℕ)(hs:0<σ)(u D E:ℕ) : ∃ η C:ℝ,0<η∧0≤C∧∀ (A:ℝ) (Y:Anthem D G)(l:ℕ),Woodsy o σ A E Y→Glyph o Y l E→e≤E→ r≤l+e→(∀ j<e,∀ p,Y p j=0) → ∃ a:Path D G, Merit Q o a l u E η (A*C)∧ a.rank=r∧ a.grade=e∧∀ p,struck a.cabin a.grade p e r=Y p e r:= by
   obtain ⟨η,C,h,hC,H⟩:= collected_bill P Q o hs r u D; obtain ⟨ξ,K,hs',hK,J⟩:= income_print (D:=D) (I:=P.Foils G r) o h r e E; refine ⟨min η ξ,C+C*K,lt_min h hs',add_nonneg hC (mul_nonneg hC hK),fun A Y l hu hc hp hl he=>?_⟩; have hA:= hu.height; let T:Studio D→ₗ[ℝ]Tile (edgeL G) r:={toFun:=fun p=> Y p e r,map_add':=fun _ _=>by rw [hc.map_add]; rfl,map_smul':=fun _ _=>by rw [hc.map_smul]; rfl}
   obtain ⟨μ,ν,hM⟩:= H T A hA (fun p=> hu.precincts e hp r p); let M:= Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T)
   refine ⟨⟨r,e,_,M⟩,⟨hp,hl, Energy.shrink hM (min_le_left ..) (?_),fun i x=> ⟨((P.fable i.1 x).2),rfl⟩, wood_mono (J M _ _ hM) (min_le_right ..) ?_ ⟩,rfl,rfl,fun p=>?_⟩
   · nlinarith only [mul_nonneg hA hC,mul_nonneg hA (mul_nonneg hC hK)]
   · nlinarith only [mul_nonneg hA hC,mul_nonneg hA (mul_nonneg hC hK)]
   rw [show struck _ _ _ _ _=candle M p r from struck_now p]; exact (print_eq P Q T h hM p hs (hu.precincts _ hp _ _) (hc.tapped hp he p) (hc.color _ _ hp p) (hc.summary.2.1 _ _ _)).symm
omit P

def binding (S:List (Path D G)):Anthem D G:= (S.map (fun a=>struck a.cabin a.grade)).sum
@[simp] lemma binding_nil : binding (D:=D) (G:=G) []=0:=by simp [binding]
@[simp] lemma binding_cons (p:Path D G)(S: List (Path D G)): binding (p::S)= struck p.cabin p.grade+binding S:=by simp [binding]
@[simp] lemma binding_fuse (P S:List (Path D G)): binding (P++S)=binding P+binding S:=by simp [binding]
structure Manus (Q:Herald)(o:Loc G 1)(S:List (Path D G))(l u E:ℕ)(σ B:ℝ):Prop where
     origin : ∀ p∈ S, Merit Q o p l u E σ B
     bill: Woodsy o σ B E (binding S)
variable {S U:List (Path D G)}
lemma Manus.intend (h:Manus Q o S l u E σ A)(hs:0<σ): Clef o (binding S) l:= by
   obtain ⟨h,-⟩:=h; induction S with
   | nil=>rw [binding_nil]; exact Clef.base
   | cons p S ih=> rw [binding_cons]; exact (struck_linear o (h p (List.mem_cons_self ..)).income hs (h p (List.mem_cons_self ..)).meets).add (ih (fun _ he=> h _ (List.mem_cons_of_mem _ he)))
lemma Manus.mounted (h:Manus Q o S l u E σ A)(hv:η ≤ σ)(he:A≤ B): Manus Q o S l u E η B:= ⟨fun _ hP=> (h.origin _ hP).increase hv he, wood_mono h.bill hv he⟩
structure Seethe (Q:Herald)(o: Loc G 1)(S:List (Path D G))(l u e E t:ℕ)(σ A:ℝ)(Y: Anthem D G):Prop extends Manus Q o S l u E σ A where
    heightp:S.length≤t
    sizes:∀ p∈S,p.grade=e ∧ p.rank<t
    lends:∀ i<t,∀ x,binding S x e i=Y x e i
lemma bindingLive (p:Studio D)(h:binding S p e t≠0):∃ a∈ S,struck a.cabin a.grade p e t≠0:= by
    induction S with
    | nil=> simp [binding] at h
    | cons a S ih=>
        by_cases hi:struck a.cabin a.grade p e t=0; swap; · exact ⟨a,List.mem_cons_self ..,hi⟩
        simp_rw [binding_cons,Pi.add_apply,hi,zero_add] at h; obtain ⟨b,hb,h⟩:=ih h;exact ⟨b,List.mem_cons_of_mem _ hb,h⟩
lemma Seethe.crisp (h:Seethe Q o S l u e E r σ A Y)(j m:ℕ)(v:Studio D)(hp:binding S v j m≠0): e≤j∧ (e=j→ m<r):= by
   obtain ⟨a,he,hk⟩:= bindingLive v hp; have hz:= h.sizes a he; have ht:= struck_right hk; omega
lemma seethe_mono (h:Seethe Q o S l u e E r σ A Y)(hv:η ≤ σ)(he:A≤B): Seethe Q o S l u e E r η B Y:= { h with toManus:=h.toManus.mounted hv he }
include P
lemma seethe (Q:Herald) (o:Loc G 1)(hs:0<σ)(u D e E t:ℕ):∃ η C:ℝ,0<η∧0≤C∧ ∀ A:ℝ,∀ (Y:Anthem D G)(l:ℕ),Woodsy o σ A E Y→ Glyph o Y l E →e≤E→(∀ j< e,∀ p,Y p j=0) → ∃ P,Seethe Q o P l u e E t η (A*C) Y:= by
    induction t with
    | zero=> refine ⟨σ,0,hs,le_rfl,fun A Y l W U he h=>⟨[],⟨by simp,by rw [binding_nil]; exact wood_zero (by simp)⟩,by simp,by simp,by simp⟩⟩
    | succ t ih=>
        obtain ⟨η,C,h,hC,H⟩:=ih; obtain ⟨ξ,K,hp,hK,J⟩:= sow_slot P Q o t e hs u D E; refine ⟨min η ξ,K+C,lt_min h hp, add_nonneg hK hC,fun A Y l W U he hh=>?_⟩
        obtain ⟨S,hS⟩:= H A Y l W U he hh; have hv:=W.height; let s:=min η ξ; have hw:=seethe_mono hS (min_le_left η ξ) le_rfl
        have hz(v:Studio D): binding S v e t=0:= by by_contra ha; exact (lt_irrefl _ ((hS.crisp e t v ha).2 rfl))
        by_cases hq:t≤l+e; swap
        · refine ⟨S,(hw.toManus.mounted le_rfl (by gcongr; exact le_add_of_nonneg_left hK)),hS.heightp.trans (by omega),fun a ha=> ⟨(hS.sizes a ha).1,Nat.lt_add_right _ (hS.sizes a ha).2⟩,fun i hi p=>?_⟩
          by_cases ht:i=t; swap;· exact hS.lends i (by omega) p
          subst i;rw [hz];symm; exact Classical.byContradiction fun hy=> hq (U.summary.1 _ _ _ hy) -- l+e
        obtain ⟨a,ha,Hr,Hg,H'⟩:= J A Y l W U he hq hh;let Hm:=ha.increase (min_le_right η ξ) le_rfl; rw [mul_add]; refine ⟨a::S,⟨fun i hi=>?_, by rw [binding_cons]; exact wood_plus Hm.costs hw.bill ⟩,List.length_cons .. ▸ Nat.succ_le_succ hS.heightp,fun x hx=>?_,fun i hi p=>?_⟩
        · rcases List.mem_cons.mp hi with rfl|hi; exact Hm.increase le_rfl (le_add_of_nonneg_right (by positivity)); exact (hw.origin i hi).increase le_rfl (le_add_of_nonneg_left (by positivity))
        · rcases List.mem_cons.mp hx with rfl|hx; exact ⟨Hg,by omega⟩; have ht:= hS.sizes x hx; omega
        rw [binding_cons, Pi.add_apply,Pi.add_apply,Pi.add_apply]; by_cases hp:i=t;subst i; rw [H',hz,add_zero]
        rw [hS.lends i (by omega) p, show struck _ _ _ e i=0 from ?_,zero_add]; by_contra hu; have hh:= struck_right hu;omega
end YM.FormalBulk08.Spigot
