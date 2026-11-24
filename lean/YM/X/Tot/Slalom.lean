import YM.X.Tot.Page
/-!
# Slalom: from dressed hor-lines cargo along F curve, rise number of separate normalized wires at any vertex, counting remaining legs. Retain cost from emission weights and color flags.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (q:ℕ+)
local notation "ε"=> epsilon q
local notation "H"=> Hair G
abbrev Billboard (G:Gauge)(q:ℕ+):= (k:ℕ)→ Site (side q k)→ Curly G
def ensign (q:ℕ+)(f:ℕ→ℂ) : Weave q:= fun i _=> f i
local notation "Ψ"=> Billboard G q
def cloak (x:Fielding.Walk): Foam G→ₐ[ℂ] Billboard G q where
    toFun p:= fun i _=> dress (x i) (p i); map_zero':= funext fun i=> funext fun j=> map_zero _; map_one':= funext fun i=> funext fun j=> map_one _; map_add' p r:=funext fun i=>funext fun _=> map_add (dress (x i)) (p i) (r i); map_mul' p r:= funext fun i=> funext fun _=> map_mul (dress (x i)) (p i) (r i); commutes' a:= funext fun i=> funext fun _=> AlgHom.commutes (dress _) a
-- billboard `vertex marking insertion` at lift exactly
def vertexLift : Foam G→ₐ[ℂ] Billboard G q where
    toFun p:= fun i z=> dress (lift z) (p i); map_zero':=funext fun i=>funext fun z=>map_zero (dress _); map_one':=funext fun i=>funext fun z=>map_one (dress _); map_add' p r:=funext fun i=>funext fun z=> map_add (dress (lift z)) (p i) (r i); map_mul' p r:=funext fun i=>funext fun z=> map_mul (dress (lift z)) (p i) (r i); commutes' a:=funext fun i=>funext fun z=> AlgHom.commutes (dress _) a
lemma cape_val (k:ℕ)(z:Site (side q k))(x:Fielding.Walk)(p:Foam G): cloak q x p k z=dress (x k) (p k):=rfl
lemma viz_val (k:ℕ)(z: Site (side q k))(p:Foam G): vertexLift q p k z=dress (lift z) (p k):=rfl
lemma cape_p (x:Fielding.Walk)(f:ℕ→ℂ)(p:Foam G): cloak q x (f • p)= ensign q f • cloak q x p:= by ext1 i; ext1 z;exact map_smul (dress (x i)) (f i) (p i)
lemma viz_p (f:ℕ→ℂ)(p:Foam G): vertexLift q (f • p)= ensign q f • vertexLift q p:= by ext1 i; ext1 z; exact map_smul (dress (lift z)) (f i) (p i)
def Vane {T:Submodule ℝ (Fan G)}(a:Bone G T)(k:ℕ)(x: Cover): H→₀ℂ:= com (tack a.k (ε k) (side q k) x a.x)
lemma gen (k:ℕ)(z:Cover){T:Submodule ℝ (Fan G)}(a:Bone G T): dress z (credit q a k)=glyph (Vane q a k z):=by rw [credit,dress_glyph,normF,map_smul]; rfl
lemma viz_credit (x:Tops G)(k:ℕ)(z:Site (side q k)): vertexLift q (credit q x) k z=glyph (Vane q x k (lift z)):= gen ..
def rise (a:Tops G) (Q:Billboard G q): Ψ:= fun i z=> Braid.edge (flow G (side q i)) (Vane q a i (lift z)) (Q i z)
local notation "Z"=> (Weave q)
variable (A B:Billboard G q) (x: Fielding.Walk)(v:Tops G) (Ω:Weave q)
lemma rise_prov : rise q v (Ω • A)= Ω • rise q v A:= by ext1 i; ext1 z; exact (Braid.edge _ _).map_smul (Ω i z) (A i z)
lemma riseₗ : rise q v (A+B) = rise q v A+ rise q v B:= by ext1 i; ext1 z; exact map_add (Braid.edge _ _) (A i z) (B i z)
lemma rise_s (a:ℂ): rise q v (a • A)=a • rise q v A:= by ext1 i; ext1 z; exact (Braid.edge _ _).map_smul a _
lemma rise_mul : rise q v (A*B)= rise q v A*B+A*rise q v B:= by
    ext1 i;ext1 z; rw [rise];let E:= flow G (side q i); change edge E _ (A i z * B i z)=_; rw [Derivation.leibniz,add_comm]; simp only [Pi.add_apply,Pi.mul_apply,smul_eq_mul,rise]; rw [mul_comm (B i z)]
@[simp] lemma rise0 : rise q v 0=0:=funext fun i=>funext fun z=> map_zero (Braid.edge _ _)
@[simp] lemma rise1 : rise q v 1=0:=funext fun i=>funext fun z=> Derivation.map_one_eq_zero _
def arrows (q:ℕ+)(x:Fielding.Walk)(l:List (Marks G × Tops G)):Weave q:= (l.map (fun t=> wire q x t.1 t.2)).prod
@[simp] lemma arrows0 : arrows q x (G:=G) []=1:=rfl
@[simp] lemma arrows_next (w:Marks G × Tops G)(l:List (Marks G × Tops G)): arrows q x (w::l)= wire q x w.1 w.2 * arrows q x l:= rfl
def Slalom (k:ℕ) (T:Set ℕ)(W:Set (Marks G)):Submodule ℂ (Billboard G q):= Submodule.span ℂ {u| ∃ (y:List (Marks G × Tops G))(p:Foam G), y.length=k ∧ p∈ Page q T W ∧ u= arrows q x y • cloak q x p}
variable (T:Set ℕ)(W:Set (Marks G))
lemma sticks (l:List (Marks G × Tops G))(hq:l.length=k) (p:Foam G)(hp:p∈Page q T W): (arrows q x l • cloak q x p)∈Slalom q x k T W:= Submodule.subset_span ⟨l,p,hq,hp,rfl⟩
def afterV (T:Set ℕ)(k:ℕ):Set ℕ:= {j|j+k∈ T}
lemma rise_pick (u:Marks G):rise q v (cloak q x (credit q u))=(wire q x u v) • (1:Billboard G q):= by ext1 i; ext1 z; rw [rise,cape_val,gen, Braid.link,treats_comm,show treats (flow _ (side q i)) (Vane q u i (x i)) (Vane q v i (lift z))=wire q x u v i z from stamps (x i) (lift z) u v (e:=epsilon q i)]; change C _ = wire q x u v i z • (1:Curly G); rw [← C_mul',mul_one]
lemma foamX (A B:Foam G)(c:ℕ→ℂ): A*(c • B)=c • (A*B):= by ext1 t; exact mul_smul_comm (c t) (A t) (B t) -- order inspect
lemma choose_p (a:Marks G)(ha:a∈W)(T T':Set ℕ)(h:∀ j∈ T,j+1∈T') (p:Foam G)(hp:p∈ Page q T W): credit q a * p∈ Page q T' W:= by
    induction hp using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,g,hg,hp,hv,rfl⟩:=hi; rw [foamX,← text_cons];
                 exact page_live q W _ g hg (fun b h=> List.mem_cons.mp h |>.elim (fun hm=>hm.symm ▸ ha) (hp b)) (h _ hv)
    | zero=> simp
    | add _ _ _ _ y t=> rw [mul_add];exact Submodule.add_mem _ y t
    | smul a b _ h=> rw [mul_smul_comm];exact Submodule.smul_mem _ _ h
end YM.PositionX.Tot
