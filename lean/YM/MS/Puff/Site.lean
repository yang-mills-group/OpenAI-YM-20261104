import YM.MS.Puff.Square
import YM.MS.Orbit.Coding
/-!
Finite implementation. Works through d derivatives Status & Pure even.Main and mark
coord. Dynamics same for all. Later evaluate by Wick raw power at each parameter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {A I W E J:Type} {p:Sector A}
variable [AddCommGroup E][ Module ℂ E ][AddCommGroup J][Module ℂ J]
def Center (p:Sector A): Submodule ℂ (BL A) := {
    carrier:= setOf (Pure p false)
    zero_mem':=Pure.zero
    add_mem':=Pure.add
    smul_mem':=fun x _ h=> Pure.smul x h }
def actor (p:Sector A): Actors ( BL A ):={
   guard:= Center p
   core:= product p
   unit:= Koszul.coin 1
   holds:= coin_pure _
   close:= fun _ h _ he=> Pure.prod h he -- expect xor simpl
   identityK:= fun _=> Eq.trans ( coin_product .. ) ( one_smul .. )
   identityR:= fun x=> ( (Pure.central (p:=p) (coin_pure 1) x).symm.trans ( by rw [coin_product,one_smul] ) )
   turns:= fun _ hx x _=> Pure.central hx x
   star_a:= fun _ _ _=> times_assoc .. }
variable (I)
def points (L:I→ Angled E): Angled ( I→ E ):={
    toFun u:= { toFun:= fun v i=> L i (u i) (v i), map_add' _ _:= funext fun _=> map_add .., map_smul' _ _:= funext fun _=> map_smul .. }
    map_add' _ _:= LinearMap.ext (fun u=> funext fun i=> map_add (( L i ).flip (u i)) _ _)
    map_smul' _ _:= LinearMap.ext (fun u=> funext fun i=>map_smul (( L i ).flip (u i)) _ _ ) }
def varied (L:I→ Linear E J) : Linear (I→E) (I→J):= {
    toFun x i:=L i (x i)
    map_add' _ _:= funext fun _=>map_add ..
    map_smul' _ _:= funext fun _=>map_smul .. }
open SplitP Engine
-- realization of algebra lift under pointwise operations
variable {M: Actors E}
def roof (M:Actors E): Actors (I→ E):={
   guard:= allIndex M.guard I
   core:= points I (fun _=> M.core)
   unit:= fun _=> M.unit
   holds:= (universe0 _).mpr fun _=> M.holds
   close:=fun _ hx _ hv=> (universe0 _).mpr fun i=> M.close _ (hx i (Set.mem_univ _)) _ (hv i ( Set.mem_univ _))
   turns:=fun x hx _ hv=> funext fun i=> M.turns (x i) (hx i (Set.mem_univ _)) _ (hv i (Set.mem_univ _))
   identityK:=fun _=> funext fun _=> M.identityK _
   identityR:=fun _=> funext fun _=> M.identityR _
   star_a:=fun _ _ _=> funext fun _=> M.star_a .. }
lemma rain (i:I) : Tether ( LinearMap.proj (R:=ℂ) i ) (roof I M) M:=⟨ rfl,fun _ _=> rfl ⟩
def Station (U:I→Engine M): Engine (roof I M):={
    move:=varied I fun i=>(U i).move
    stays:=fun _ h=> (universe0 _).mpr fun i=> ( U i ).stays _ ( h i ( Set.mem_univ _ ) )
    unitLaw:= funext fun i=>( U i ).unitLaw
    join:= points I (fun i=>( U i).join)
    compatibility _ _ hF hH:= funext fun i=>( U i ).compatibility _ _ ( hF i (Set.mem_univ _) ) ( hH i (Set.mem_univ _) )
    leib _ _ _ hF hH hp:= funext fun i=>( U i ).leib _ _ _ ( hF i (Set.mem_univ _) ) ( hH i (Set.mem_univ _) ) ( hp i ( Set.mem_univ _) ) }
namespace HeatFlow
variable {F H:BL A}[Fintype A]
def Baker (P:Grain A)(h: Clear p P) : Engine ( actor p ):={
    move:= Cog.frame P
    unitLaw:= by ext; simp [Cog.frame,actor,Koszul.coin]
    join:= tokenL (Cog.frame P) false p
    stays:= fun _ he=> Cog.fr_pure h false he
    compatibility f g he _:= by
       let U:= Cog.frame P; change U ( product p _ _ )=product p ( U f ) g +product p f ( U g )+ _; rw [Koszul.link_even (b:=false) U he]; change _=_+link U false p f g; abel
    leib f g k hG hF hK:= by
       change link (Cog.frame P) false p f (product p g k)=product p ( link ( Cog.frame P ) false p f g ) k + product p g (link ( Cog.frame P ) false p f k); unfold Cog.frame; simp_rw [link_sum, link_scale,map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, ← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; by_cases he:P i j=0; simp [he]; rw [ pair_products i j (by simp [h i j he]) hG hF, smul_add ] }
-- derivative along time OStatus

omit [Fintype A] in
lemma hop {J:ℝ→ Shared A ℂ} (H: Shared A ℂ) (l:Legs A)(t:ℝ)(hx:∀ u v:Legs A,Split u v l→ HasDerivAt (fun t=> J t u v) (H u v) t): HasDerivAt (fun t=> scatter p l (J t)) (scatter p l H) t:= by induction l generalizing H J with| nil=>exact hx _ _ .nil| cons i l ih=> exact ih (J:=fun t u v=>J t (i::u) v+cross (p i) (degree p u) *J t u (i::v)) (fun u v=> H (i::u) v+_ * _) (fun u v he=> (hx _ _ he.left).add ((hx _ _ he.right).const_mul _) ) -- placeholder metavars

omit [Fintype A] in
lemma lead_pair {F H:OM A}{f g:BL A}{t:ℝ}(hx:Lead F f t)(ht: Lead H g t): Lead (fun i=> product p ( F i ) ( H i )) (product p f (H t)+product p (F t) g) t:= by
    intro l; simp_rw [Pi.add_apply,scattered]; let P:=allocate p l (R:=ℂ); change HasDerivAt _ ( P _ + P _ ) _; rw [← map_add]; refine hop _ l t ( fun a b _=>?_ ); exact (hx a).mul (ht b)

def deriv (p:Sector A): Dynamics ( roof ℝ ( actor p ) ):={
    valid:=Status, mono:=⟨ ⟨0,fun i l h=>by cases l with| nil=> simp at h | cons i l=> rfl ⟩, fun _ _=> hasDerivAt_const .. ⟩, empty:= status_0 _
    plus _ _ _ _ := status_plus
    price _ _ v h:= status_cast h v
    duop _ _ _ _ h hv:= by
       obtain ⟨k,hk⟩:= h.life; obtain ⟨n,hn⟩:= hv.life; refine ⟨ ⟨ k+n,fun i=> ?_⟩,fun _=> lead_pair ( h.path _) ( hv.path _ ) ⟩; push_cast; exact ( hk i ).pair (hn i) }
end HeatFlow
end YM.MS.Puff
