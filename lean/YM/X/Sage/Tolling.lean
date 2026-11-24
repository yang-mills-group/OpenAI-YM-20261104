import YM.X.Sage.Round
/-!
# mateT. Fixed-beam rise. single(length) rebase selection. Includes non-horizontal potential.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k m:ℕ} {V I:Type*} {q:ℕ+}{r R:ℝ}
local notation "Θ"=> Reed.Horizontal G
local notation "U"=> G.ColorIndex
local notation "P"=> Curly G
local notation "Ω"=> Foam G
local notation "o"=> side q k
local notation "Q"=> qu q G k
local notation "ε"=> epsilon q k
variable (x y z:Fielding.Walk)(i:Tops G)(b:Marks G)(F:Foam G)
local notation "S"=> (Stool G)
def poke (q:ℕ+)(x y:Fielding.Walk)(i:Tops G)(F:Foam G):Ω := fun k=> dress (-(y k)) (edge (qu q G k) (Vane q i k (x k)) (veil (y k) k F))
local notation "D" => poke q x y i
lemma dressed : veil (y k) k (D F)= edge Q (Vane q i k (x k)) (veil (y k) k F):= by rw [veils,poke, dress_addT,add_neg_cancel,dress_zero]
lemma veil_ext (a b:Foam G)(h:∀k:ℕ,veil (x k) k a=veil (x k) k b):a=b:= by
    ext1 k; have ht:= congr_arg (dress (-(x k))) (h k); simp only [veils,dress_addT,neg_add_cancel,dress_zero] at ht; exact ht
lemma veil_up (a:ℕ→ℂ)(v:Cover): veil v k (a • F)=a k • veil v k F:= map_smul (dress _) (a k) _
lemma wakeberry_1 : D 1=0:= veil_ext y _ _ (fun k=> by rw [dressed,map_one,map_zero]; exact Derivation.map_one_eq_zero _)
lemma wakeberry_0 : D 0=0:= veil_ext y _ _ (fun k=> by rw [dressed,map_zero,map_zero])
lemma awake (G':Foam G): D (F+G')= D F+D G':= veil_ext y _ _ (fun k=> by rw [dressed,map_add,map_add,map_add,dressed,dressed])
lemma awake_scale (c:ℕ→ℂ): D (c • F)= c • D F:= veil_ext y _ _ (fun k=> by rw [dressed,veil_up,veil_up,dressed,Derivation.map_smul])
lemma awake_mul (G':Foam G): D (F*G')=D F*G'+F*D G':= by
   apply veil_ext y; intro k; rw [dressed,map_add]; simp only [map_mul (veil (y k) k)]; rw [dressed,dressed,Derivation.leibniz]; simp only [smul_eq_mul]; ring -- module? algebra via simp smul
abbrev cartT (q:ℕ+)(x y:Fielding.Walk)(i:Tops G)(b:Marks G)(k:ℕ):ℂ:= entryK (side q k) (epsilon q k) (y k) b (x k) i
lemma cart_real : cartT q x y i b k=↑(cable q y x (b.k+i.k) (pathS b.x i.x) k):= feeK b i (y k) (x k) (epsilon_pos ..)
lemma awake_cart : D (credit q b)= cartT q x y i b • (1:Foam G):= by apply veil_ext y; intro k; rw [dressed, veils (p:=credit q b),gen, link,treats_comm,veil_up,map_one, show ∀ c:ℂ, c • (1:Curly G)= MvPolynomial.C c from fun c=> by rw [← C_mul', mul_one]]; exact congr_arg _ (stamps (y k) (x k) b i)
local notation "K"=> cartT q x y
variable (hq:1<q.val)(h:Clear q R y x)(hr:0≤R)
include hq h hr
lemma orbitB : Released (K i b):= by
    obtain ⟨y',x',hy,hx,H⟩:=h; rw [funext (fun k:ℕ=> cart_real (q:=q) (k:=k) x y i b)]; exact Released.lin Complex.ofRealCLM.toLinearMap (floated hq (sub_ne_zero.mp (norm_pos_iff.mp (lt_of_le_of_lt hr H))) hy hx _ (air_rank _ _ b.order i.order)) -- order
lemma mono_raise (T:Set S)(l:List (Marks G))(ht:∀ v∈l,v∈T)(he:m=l.length-1):D (textA q l)∈single q m T:= by
    rw [he]; clear he; induction l with
    | nil=> rw [Tot.empty,wakeberry_1]; exact Submodule.zero_mem _
    | cons a l ih=>
       simp_rw [text_cons,awake_mul,awake_cart]; rw [List.length_cons,Nat.add_sub_cancel_right, show (_ • (1:Foam G))*_= cartT q x y i a • textA q l from ?_]; swap; · rw [mul_comm, foamX,mul_one]
       refine Submodule.add_mem _ (page_scale _ _ (orbitB x y i a hq h hr) (page_spec _ _ _ (fun j hj=>ht j (by simp [hj])) rfl)) ?_; cases l with
       | nil=> rw [Tot.empty,wakeberry_1,mul_zero]; exact Submodule.zero_mem _
       | cons b l=> have h':1+((b::l).length-1)=(b::l).length:= by rw [List.length_cons]; omega
                    refine single_mulK h'.symm (credit_lean _ T a (ht _ (by simp)) rfl) (ih (fun j hj=>ht j (by exact List.mem_cons_of_mem _ hj))) -- indentation
lemma awaken (T:Set S)(he:F∈single q (m+1) T): D F∈single q m T:= by
    induction he using Submodule.span_induction with
    | mem v hv=> obtain ⟨l,c,H,h0,h',rfl⟩:=hv; rw [awake_scale]; exact page_scale q T H (mono_raise x y i hq h hr T l h0 (by change l.length=m+1 at h';omega))
    | zero=> rw [wakeberry_0];exact Submodule.zero_mem _
    | add a b _ _ s t=> rw [awake]; exact Submodule.add_mem _ s t
    | smul c a h t=> rw [show c • a=(fun _:ℕ=> c) • a from rfl, awake_scale]; exact Submodule.smul_mem _ c t
lemma awakes {T:Set S}(he:F∈single q d T)(hm:d=m+1): D F∈single q m T:= awaken x y i F hq h hr T (hm ▸ he)
end YM.PositionX.Sage
