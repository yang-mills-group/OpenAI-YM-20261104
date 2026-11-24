import YM.MS.Orbit.Tassel
/-!
# Strictly periodic smooth extension to doubled branches. Morphisms to finite nets, not differentiated guards. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux
open scoped Topology ContDiff Interval
variable {G:Gauge}{K: Latch.Edge G}{F H:Law G}{f x y z u v:Lengths G}{E A:Type}{pQ q:QP}{n:Side}
local notation "Z"=> field (parity ( A:=Axis ) ( C:=G.ColorIndex))
abbrev peer (x y: Lane4 G): Prop:= x.1=y.1∧ congrQ x.2 y.2
abbrev twins (x y:Lengths G): Prop:= List.Forall₂ peer x y
abbrev Speaks (F:Law G): Prop:= ∀ x y,twins x y→ F x=F y
abbrev SpeaksK (K: Latch.Edge G): Prop:= ∀ i j,pinQ ( K i j )
lemma asc (q:Lengths G): twins q q:= by induction q with| nil=> exact .nil| cons x l ih=>exact .cons ⟨rfl,congrQ.normal _⟩ ih
lemma useW (F: Law G) (h:∀ l x y z, peer x y→ F (l++ x::z)=F (l++y::z)): Speaks F:= by
   intro l r hl; suffices he:∀ u:Lengths G, F (u++l)=F (u++r) by simpa using he []
   induction hl with
   | nil=> exact fun _=>rfl
   | @cons a b s t he hx ih => intro u; rw [ h u a b s he ]; simpa only [List.append_assoc, List.cons_append,List.nil_append] using ih (u++[b])
lemma volt (H:Perk F): Speaks (sleeve lace F):= by
   apply useW; intro l i j r Ht; rcases i with ⟨i,x⟩; rcases j with ⟨j,y⟩; obtain ⟨rfl,z,rfl⟩:= (show i=j ∧ ∃ z: Cover,x=y+rep z from Ht); simp only [sleeve_here,hook,List.map_append,List.map_cons,List.prod_append,List.prod_cons,laceR]; rw [ H ]; ring_nf; simp [pow_two,testX]
lemma speak_d (h:City.Near K): SpeaksK (dope K):= fun _ _ _ _ hx=> Dk_near h _ _ _ _ hx -- `_x`
lemma speak0 : Speaks (0:Law G):= fun _ _ _=> rfl
lemma speak_add (h:Speaks F)(hv:Speaks H): Speaks ( F+H ):=fun x y hK=> by simp only [Pi.add_apply,h x y hK,hv x y hK]
lemma speak_smul (h:Speaks F)(z:ℂ): Speaks ( z • F ):=fun x y hP=> by simp only [Pi.smul_apply,h x y hP]
lemma speak_sum (S:Finset E) (W:E→Law G)(H:∀ i∈ S, Speaks (W i)): Speaks (∑ i∈S,W i):=fun x y hp=> by rw [Finset.sum_apply, Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> H i hi x y hp
lemma n_cast (h:twins x y): congrQ (net x) (net y):= by induction h with| nil=>exact congrQ.normal _| cons hh he ih=> exact hh.2.plus ih
lemma d_cast (h: twins x y): degree Z x= degree Z y:= by induction h with| nil=>rfl| cons H hv ih=> exact congr_arg₂ Bool.xor (congr_arg parity H.1) ih
lemma scatter_twins {X Y: Shared (Mode (BH G) QP) ℂ} (hp: twins u v)(he:∀ x y l r,twins x l→twins y r→X x y=Y l r): scatter Z u X = scatter Z v Y:= by
   induction hp generalizing X Y with| nil=> exact he _ _ _ _ (asc _) (asc _)| cons ht hv ih=> exact ih (fun x y l r hx hy=> by rw [ d_cast hx, he _ _ _ _ (.cons ht hx) hy, he _ _ _ _ hx (.cons ht hy),show Z _ = Z _ from congr_arg parity ht.1]) -- degree uses l not r inspect
lemma pin_T (hk:SpeaksK K) (h:Speaks F) (he:Speaks H): Speaks ( tree parity K F H ):= by
   intro x y hP; apply scatter_twins hP; intro x y u v hM hK; unfold attaches; obtain hQ:= n_cast hM; simp only [ neg_neg, d_cast hM,hk _ _ hQ.opp,hk _ _ hQ ]; simp_rw [show ∀i, F ((i,-net x)::x)= _ from fun i=> h ((i,-net x)::x) ((i,-net u)::u) (.cons ⟨rfl,hQ.opp⟩ hM), show ∀j,H ((j,net x)::y)=_ from fun j=> he ((j,net x)::y) ((j,net u)::v) (List.Forall₂.cons ⟨ rfl,hQ⟩ hK) ]; -- elaboration
-- finite maps preserving λ via LiftM.H sigma root images. Pref approximation.
abbrev FixedMode (G:Gauge)(n:Side):= Mode (BH G) (Site n)
abbrev Than (G:Gauge)(n:Side):= Raw (FixedMode G n) ℂ
abbrev addr (i:FixedMode G n): Lane4 G:= ⟨i.1,Coord i.2⟩
abbrev stage (w:Legs (FixedMode G n)):= w.map addr
def rentS (G:Gauge)(n:Side): Law G→ₗ[ℂ] Than G n:={
    toFun F:= F∘ stage
    map_add' _ _:= rfl
    map_smul' _ _:= rfl }
lemma θ_net (w:Legs (FixedMode G n)): congrQ (net (stage w)) ( Coord (net w) ):= by
    induction w with| nil=>change congrQ 0 ( Coord (0:Site n) ); rw [ξ_zero]; exact congrQ.normal _| cons i l ih=> unfold stage; rw [ List.map_cons,net_cons,net_cons (x:=i) ]; exact (( congrQ.normal _ ).plus ih)|>.trans (ξ_add ..)
lemma Λ_d (w:Legs (FixedMode G n)): degree Z (stage w)=degree Z w:= by induction w with| nil=>rfl| cons i l h=> exact congr_arg₂ Bool.xor rfl h
end YM.MS.Orbit
