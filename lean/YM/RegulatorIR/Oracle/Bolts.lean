import YM.RegulatorIR.Oracle.Credited

/-! tree walk budgets. coarse boxes not necessarily locally injective.
Exact charge in any size including non-ranking $n$. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p: Side}(P:Patch)(H:KernelChoices)

-- coherent arbitrary n forest from coordinates. independence on p
def stemF (n:Side): Tree.Forest (tileB P.L n):=bios (avenue P ⟨1,1,1,1,zero_lt_one,zero_lt_one,zero_lt_one,zero_lt_one⟩ n)
lemma boleT (n:Side):stemF P n=bios (avenue P H n):=rfl

def rentW (L:Side) (x:Cover): Cover:= ((claims L).symm x).1
lemma wageS (L:Side)(n:Side)(x:Cover): (tileB L n).parent (wrap (n*L) x)= wrap n (rentW L x):=by
 obtain ⟨⟨u,s⟩,rfl⟩:= reachesR L x; rw [tile_r];rw [Ratio.assemble_parent]; exact Eq.symm (congr_arg (wrap n) (congr_arg Prod.fst ((claims L).symm_apply_apply (u,s))))
lemma rent_add (L:Side)(n y:Cover): rentW L (L.val • n+y)=n+rentW L y:=by
 obtain ⟨⟨x,z⟩,rfl⟩:= reachesR L y; have hp x: rentW L (child L x z)=x:=congr_arg Prod.fst ((claims L).symm_apply_apply (x,z))
 rw [show L.val • n+_=child L (n+x) z from ?_,hp]; rw [hp]
 unfold child; rw [smul_add,add_assoc]
private lemma leaf_point (x:Cover) : leaf (tileB P.L p) (wrap _ x) ↔ leaf (tileB P.L n) (wrap _ x):=by unfold leaf; simp only [ne_eq,Ratio.root_id,Ratio.residue_wrap]; rfl
private lemma pin_u (x:Cover) : slot (tileB P.L p) (wrap _ x)=slot (tileB P.L n) (wrap _ x):= by unfold slot; rw [Ratio.residue_wrap,Ratio.residue_wrap];rfl
private lemma step_move (x:Cover): (stemF P p).up (wrap (p*P.L) x)=(stemF P n).up (wrap (n*P.L) x):=by
 let R:=tileB P.L p;let S:=tileB P.L n
 let z:=wrap (p*P.L) x;let y:=wrap (n*P.L) x
 change (if h:leaf R z then toward R z h else posDir 0)=(if h : leaf S y then toward S y h else _)
 split
 next h=>
   let v:= (leaf_point P (p:=p) (n:=n) x).mp h; rw [dif_pos v];
   have ht: Bark.slim R z h=Bark.slim S y v:=by unfold Bark.slim; congr 1; unfold Bark.active; rw [show slot R z=slot S y from pin_u P x]
   unfold toward; rw [ht,show slot R z=slot S y from pin_u P x]
 next h=> rw [dif_neg (fun hx=>h ((leaf_point P x).mpr hx))]
lemma walks (n p:Side)(x:Cover): (stemF P p).hike (wrap (p*P.L) x)=(stemF P n).hike (wrap (n*P.L) x) :=by
 let A:=stemF P p;let B:=stemF P n
 suffices ∀ y:Site (p*P.L),∀ x:Cover,y=wrap (p*P.L) x→ A.hike y=B.hike (wrap (n*P.L) x) from this _ x rfl
 intro y; induction y using Forest.hike.induct A with
 | case1 a ha ih=>
    rintro t rfl
    have h:= (leaf_point P t (p:=p) (n:=n)).mp ha
    let f:=p*P.L;let g:= n*P.L;let d:= A.up (wrap f t)
    conv_lhs=>rw [Forest.hike,dif_pos ha]
    conv_rhs=>rw [Forest.hike,dif_pos h]
    change d::_=B.up _ :: B.hike _;have hx:= ih (t+d.vec) (show wrap f t+d.vec= _ from (by rw [_root_.map_add, wrap_vec]))
    have ht:B.up (wrap g t)=d:= step_move P t;rw [ht, hx,_root_.map_add, wrap_vec]
 | case2 a ha=> rintro t rfl; rw [Forest.hike,dif_neg ha,Forest.hike,dif_neg (fun h=>ha ((leaf_point P t).mpr h))]
lemma paths_cs (n:Side)(x:Cover)(d:Cover):
 (stemF P n).hike (wrap (n*P.L) (P.L.val • d+x))=(stemF P n).hike (wrap (n*P.L) x):=by
 let A:=stemF P n;let g:=tileB P.L n
 let y:=wrap n d
 have hv(z:Site (n*P.L)): A.hike (z+g.embed y)=A.hike z:=by
    induction z using Forest.hike.induct A with
    | case1 z hz ih=> rw [Forest.hike,dif_pos ((Fibers.shifted_leaf g z y).2 hz),show A.up _= A.up z from repeat_patch g P.odd_side z y,show z+g.embed y+_=z+((A.up z).vec)+(g.embed y) from add_right_comm ..,ih]; rw [show A.hike z=_ from ?_];rw [Forest.hike,dif_pos hz]
    | case2 z hz=>rw [Forest.hike,dif_neg (fun h=>hz ((Fibers.shifted_leaf g z y).1 h)), Forest.hike, dif_neg hz]
 rw [add_comm,_root_.map_add, show wrap (n*P.L) (P.L.val • d)=g.embed y from (g.embed_wrap d).symm]; exact hv _
-- irrespective of n return enough to know stencil0
lemma trunksW (x:Edge Cover) : around (p*P.L) x∈ (stemF P p).trunks ↔ around (n*P.L) x∈(stemF P n).trunks:=by
 -- transfer via lags
 have he(p n:Side): around (p*P.L) x∈ (stemF P p).trunks → around (n*P.L) x∈(stemF P n).trunks:=by
    intro h; obtain ⟨y,hy,hx⟩:= ((stemF P p).trunk_mem_iff ..).mp h; let T:=stemF P p;let U:=stemF P n
    let f:=p*P.L; let g:=n*P.L
    let k : Lattice.Step:= T.up y
    change k.used y= around f x at hx; unfold Lattice.Step.used at hx; apply (U.trunk_mem_iff _).mpr; split at hx
    next h=>
       have hb:y=wrap f (x.1+step k.dir):=by rw [_root_.map_add,wrap_step]; exact sub_eq_iff_eq_add.mp (show y-step k.dir= _ from congr_arg Prod.fst hx) -- fix
       let z:= wrap g (x.1+step k.dir)
       have ht:U.up z=k:=by unfold k; rw [hb]; exact step_move P ..
       refine ⟨z,(leaf_point P _).mp (hb ▸ hy),?_⟩
       rw [ht]; unfold Lattice.Step.used; rw [if_pos h]; exact Prod.ext (by change wrap g (_+_)-_= _;rw [_root_.map_add,wrap_step,add_sub_cancel_right];rfl) (congr_arg (Prod.snd : Edge (Site f)→Axis) hx)
    next h=>
       have he:y=wrap f x.1:=congr_arg Prod.fst hx; let z:=wrap g x.1
       have ht:U.up z=k:=by unfold k; rw [he]; exact step_move P ..
       refine ⟨z,(leaf_point P _).mp (he ▸ hy),?_⟩
       rw [ht]; unfold Lattice.Step.used; rw [if_neg h]; exact Prod.ext rfl (congr_arg (Prod.snd : Edge (Site f)→Axis) hx)
 exact ⟨he _ _,he _ _⟩
end YM.RegulatorIR.Oracle
