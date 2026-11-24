import YM.X.Tot.Final
import YM.X.Tot.Hem
import YM.X.Tot.Bow
import YM.X.Chir.Sign
/-!
# Spin and lattice-explicit Cov kernels along any tiles. Internal unnormalized signs. upper/negative chosen, real. exact layout.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}
local notation "s₀"=> Finsupp.single
local notation "U"=> G.ColorIndex
variable (i j k':Axis)(a b: G.ColorIndex)(r:ℝ)
def columnA (i:Axis)(a:G.ColorIndex): Tops G:= ⟨0,s₀ ((0,i),a) 1,by rw [grade0];simp,by simp⟩
abbrev diffA (i j:Axis)(a:G.ColorIndex):= jetRow 1 (fun _=>i) ((0,j),a)
lemma arc_diff : arc a 0 i j = diffA i j a-diffA j i a:= by unfold arc diffA; simp only [jetRow]; abel
def slope (r:ℝ)(p:Tet)(a:G.ColorIndex) : Fan G:= ∑ i:PlaqAxes, form r p i.val.1 i.val.2 • signal_arc (0,i,a)
lemma slope_h (p:Tet): slope r p a∈ Reed.Horizontal G:=
    (Reed.Horizontal G).sum_mem fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
lemma slope_k(p:Tet): slope r p a∈ Reed.grads G 1:=
    Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (arc_occ _)) -- maybe unfold
lemma descent (p:Tet): slope r p a = ∑ j:Axis,∑ k:Axis, form r p j k • diffA j k a := by
    let f(j k:Axis):= form r p j k • diffA j k a; change _=∑ j, ∑ k,f j k; rw [← plaq_turn f (by intro i; unfold f; rw [straight, zero_smul])]; apply Finset.sum_congr rfl; intro i _; unfold f; let u:= i.val.1; let v:=i.val.2; change form r p u v • arc a 0 u v = _; rw [arc_diff i.val.1 i.val.2 a,layout r p i.val.2 i.val.1,smul_sub,neg_smul]; abel

def spin (r:ℝ)(p:Tet)(a:G.ColorIndex): Marks G:= ⟨1,slope r p a,slope_k a r p,slope_h a r p⟩
def upMark (u:Marks G):Tops G:= ⟨u.k,u.x,u.order,by simp⟩
-- GridLi measure native plate. x mark to y. Leading piece unormalized spin G2 scaled
abbrev Scaff : Type:= (n:Side)→Site n→Site n→ℝ
def castG : Scaff→ₗ[ℝ] GridF where
   toFun B n x y:= B n (wrap n x) (wrap n y); map_add' _ _:=rfl; map_smul' _ _:=rfl
def air (k:ℕ):Submodule ℝ Scaff:= (bird k).comap castG
lemma sky {D:Scaff}: D ∈ air m ↔ castG D ∈ bird m:= Iff.rfl
lemma cast_inj : Injective castG:= fun x y h=> funext (fun n=> funext (fun z=> funext (fun t=> by
    simpa [castG] using (congr_fun (congr_fun (congr_fun h n) (lift z)) (lift t)))))
def graphS (D:List Axis)(x:Cover): Scaff:= fun n y z=> Interval.grads D green (y-z+wrap n x)
lemma cast_graph (l:List Axis)(x:Cover): castG (graphS l x)=graphK l x := by ext n z y; simp [castG,graphK,graphS]
lemma air_graph(l:List Axis)(x:Cover)(he:l.length=k):graphS l x∈ air k:= sky.mpr (cast_graph l x |>.symm ▸ graph_bird l x he)

def pathS (f g:Fan G): Scaff:= fun n x y=> spend n (lift x) (lift y) f g
lemma spend_eq_x (f g:Fan G){x y z:Cover}(h:wrap n x=wrap n y): spend n x z f g=spend n y z f g:= by
    suffices h: spend (G:=G) n x z=spend n y z by rw [h]
    ext p r; simp only [LinearMap.comp_apply,Finsupp.lsingle_apply]; rw [spend_single,spend_single]; unfold tau Braid.cane pointB; simp only [map_add,h]
lemma cast_path (f g:Fan G): castG (pathS f g)= fun n x y=> spend n x y f g:= by ext n x y; unfold castG pathS; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [spend_eq_x f g (x:=lift _) (y:=x) (wrap_lift _),Fielding.symmetry x,spend_eq_x g f (x:=lift _) (y:=y) (wrap_lift _),Fielding.symmetry y]
lemma air_rank (f g:Fan G)(h:f∈Reed.grads G k)(ht:g∈Reed.grads G m): pathS f g∈ air (k+m):= sky.mpr (cast_path f g|>.symm ▸ enrolled₂ f g h ht) -- rank
lemma path_eq (x y:Cover)(f g:Fan G): pathS f g n (wrap n x) (wrap n y)=spend n x y f g:= congr_fun (congr_fun (congr_fun (cast_path f g) n) x) y
-- B structure colors Kronecker rule can computationally reduce small symbols
lemma column_d (x y:Cover)(l:Fin k→Axis): spend n x y (jetRow k l ((0,j),b)) (columnA i a).x = if i=j ∧ a=b then graphS (ls k l) 0 n (wrap n x) (wrap n y) else 0:= by
    change spend n x y _ (jetRow 0 Fin.elim0 ((0,i),a))=_; rw [dictate,pow_zero,one_mul,ls,markS,sub_self,sub_zero,List.append_nil,←cast_graph]; unfold matchK; simp only [ite_mul,one_mul,zero_mul]; dsimp only [castG,LinearMap.coe_mk,AddHom.coe_mk]; simp [eq_comm,and_comm]
end YM.PositionX.Chir
