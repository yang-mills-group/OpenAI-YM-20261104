import YM.X.Tot.Slalom
/-! # rise through arbitrary number of strands. Tag remembers vertex vs mark class. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable {q:ℕ+}
local notation "H"=> Hair G
local notation "Ψ"=> Billboard G q
local notation "K"=> Weave q
variable (T:Set ℕ)(W:Set (Marks G))(x:Fielding.Walk) {a: Marks G}
variable (q)
def bladeC (A:Weave q) : Module.End ℂ (Billboard G q) where
   toFun p:= A • p; map_add' p s:= smul_add _ _ _; map_smul' t p:= smul_comm A t p
lemma blade_val(A: Weave q) (p:Billboard G q): bladeC q A p=A • p:=rfl
lemma stack {A : Billboard G q} (h:a∈W)(T T':Set ℕ)(hp:∀ i∈ T,i+1∈T') (he:A∈Slalom q x k T W) : cloak q x (credit q a)*A∈Slalom q x k T' W:= by
    induction he using Submodule.span_induction with
    | mem p he=> obtain ⟨l,v,ht,hk,rfl⟩:=he; rw [show cloak q x (credit q a)*(arrows q x l • cloak q x v)=arrows q x l • (cloak q x (credit q a)*cloak q x v) from mul_smul_comm ..,← map_mul]; exact sticks q x T' W l ht _ (choose_p q W a h _ _ hp v hk)
    | zero=> simp
    | add a b _ _ u v=> rw [mul_add]; exact Submodule.add_mem _ u v
    | smul t a _ h=> rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
lemma launch_(A: Foam G)(h:A∈ Page q T W): cloak q x A∈Slalom q x 0 T W:= by rw [← one_smul K (cloak q x A), ← arrows0 (G:=G) q x]; exact sticks q x T W [] rfl _ h
lemma boost (Ω:ℕ→ℂ)(H':Released Ω){A:Billboard G q}(h:A∈Slalom q x k T W): ensign q Ω • A∈Slalom q x k T W:= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,p,ht,hp,rfl⟩:=hi; rw [smul_comm, ← cape_p]; exact sticks q x T W l ht (Ω • p) (page_scale q _ H' hp)
    | zero=> simp
    | add x y _ _ v t=> rw [smul_add];exact Submodule.add_mem _ v t
    | smul a p _ h=> rw [smul_comm];exact Submodule.smul_mem _ _ h
lemma defer (l:List (Marks G × Tops G)){A:Billboard G q}(h:A∈Slalom q x k T W) : arrows q x l • A∈ Slalom q x (l.length+k) T W:= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨m,v,ht,h',rfl⟩:=hi; rw [smul_smul,show arrows q x l * arrows q x m= arrows q x (l++m) from by simp only [arrows,List.map_append,List.prod_append]]; exact sticks q x T W _ (by simp [ht]) _ h'
    | zero=> simp
    | add a b x y u v=> rw [smul_add];exact Submodule.add_mem _ u v
    | smul t v _ h=> rw [smul_comm]; exact Submodule.smul_mem _ _ h
variable (b:Tops G)(l:List (Marks G))
lemma pick_step (hp:∀a∈l,a∈W)(ht:l.length∈T): rise q b (cloak q x (textA q l))∈ Slalom q x 1 (afterV T 1) W:= by
    induction l generalizing T with
    | nil=> simp
    | cons a l IH=>
       let S:= afterV T 1; let C:=Slalom q x 1 S W; rw [text_cons,map_mul,rise_mul,rise_pick]; refine C.add_mem ?_ ?_; have h₁(i:Marks G)(h:i∈l):i∈ a::l:=List.mem_cons_of_mem _ h
       · rw [smul_mul_assoc,one_mul]; let u:Marks G × Tops G:=(a,b); have H' : arrows q x [u]=wire q x a b:=by simp [u]
         rw [← H']; exact sticks q x S W [u] rfl _ (page_spec q W l (fun i h=>hp i (List.mem_cons_of_mem _ h)) ht) -- order hv after
       exact stack q W x (hp a (by simp)) (afterV S 1) S (fun i h=>h) (IH S (fun i h=>hp i (List.mem_cons_of_mem _ h)) ht)
lemma pick (p: Foam G)(h:p∈ Page q T W) : rise q b (cloak q x p) ∈ Slalom q x 1 (afterV T 1) W:= by
    induction h using Submodule.span_induction with
    | mem p hp=> obtain ⟨l,v,t,h,h',rfl⟩:=hp; rw [cape_p,rise_prov]; exact boost q (afterV T 1) W x _ t (pick_step q T W x b l h h')
    | zero=> simp
    | add a b _ _ x y=> rw [map_add, riseₗ]; exact Submodule.add_mem _ x y
    | smul a p _ h=> rw [map_smul,rise_s]; exact Submodule.smul_mem _ _ h
lemma pickS (A:Billboard G q)(h:A∈ Slalom q x k T W): rise q b A ∈ Slalom q x (k+1) (afterV T 1) W:= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,v,h,hp,rfl⟩:=hi; rw [rise_prov,←h]; exact defer q (afterV T 1) W x l (pick q T W x b v hp)
    | zero=> simp
    | add a b _ _ x y=> rw [riseₗ]; exact Submodule.add_mem _ x y
    | smul a p _ h=> rw [rise_s];exact Submodule.smul_mem _ _ h
end YM.PositionX.Tot
