import YM.RegulatorIR.Oracle.Publication
import YM.Push.FREE_RESOLVENT.FullRow
import YM.RegulatorIR.Sources.Child

/-! Finest relative kernel quarries. Full coarse/patch/$L$ parameter.
Physical predictor proof orientation later (not a canonical projection arbitrary). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Pert.Bulk Sources Tree Tree.Forest PertExtension Geometry Geometry.Field 
open FreeResolvent (Slot PAC)
open Exterior RG
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {G: Gauge} {X Y A : Type} {S : Side→Type}

def tileB (L c:Side): Ratio c (c*L) := ⟨L,rfl⟩
lemma tile_r {L p:Side} (x:Cover)(s:Site L): wrap (p*L) (Sources.child L x s)=(tileB L p).assemble (wrap p x,s):=by
 unfold Ratio.assemble Sources.child; rw [Ratio.embed_wrap,map_add]; rfl
-- Fine figures. Unitary PAC orientation slots 1


def geological (L:Side)(A:Type): Quarry (Market A) (Co L A) (fun i=>Co (i*L) A) := ⟨((Equiv.prodCongr (claims L).symm (Equiv.refl A)).trans (Equiv.prodAssoc _ _ _)),fun i=> Bloch.splitCo (tileB L i) A⟩

def groundM (A:Type): Quarry (Market A) A (fun i=>Co i A):=⟨Equiv.refl _,fun _=> Equiv.refl _⟩
lemma landFull (L:Side)(x:Cover)(s:Site L)(i:A) : (geological L A).toFull (child L x s,i)=(x,s,i):=by
 let p:=(claims L).symm (child L x s); change (p.1,p.2,i)= _; rw [show p=(x,s) from (claims L).symm_apply_apply (x,s)]
lemma clamped (n L:Side)(x:Market A) : (geological L A).swrap n x=(wrap (n*L) x.1,x.2):=by
 rcases x with ⟨x,i⟩;obtain ⟨⟨v,y⟩,hx⟩:= reachesR L x;rw [← hx]; let W:= geological L A; change W.swrap n (child L v y,i)=(wrap _ (child L v y),i)
 unfold Quarry.swrap Quarry.boom Quarry.cabin W; rw [landFull,tile_r]
 exact (show ((tileB L n).splitSites.symm ( (wrap n v),y),i)=_ from rfl)
lemma c_shift (x:Market A)(L:Side)(d:Cover): (geological L A).shiftB d x=(L.val • d+x.1,x.2):=by
 rcases x with ⟨x,i⟩;obtain ⟨⟨v,y⟩,hx⟩:= reachesR L x;subst x; let W:=geological L A; apply W.toFull.injective; rw [W.to_shift]; dsimp only
 have ht: L.val • d+child L v y=child L (d+v) y:=by unfold child;rw [smul_add,add_assoc]
 change (d+W.boom (child L v y,i),W.cabin (child L v y,i)) = W.toFull (L.val • d+child L v y,i) -- 
 rw [ht]; dsimp only [boom,cabin]; rw [landFull,landFull]
lemma blockT (L:Side)(c:Side): Odd (tileB L c).count.val↔ Odd L.val:=Iff.rfl
-- Long link basis and Co
variable (G)
def site_eq : Long G.ColorIndex≃ Market (PAC G 1) := (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _)))
lemma site_at (a:Long G.ColorIndex) : site_eq G a=(a.1.1,coord a.1.2, a.2):=rfl

def linksQ : Quarry (Long G.ColorIndex) (PAC G 1) (fun n=>Slot G n 1) := ⟨site_eq G,fun n=> (groundM (PAC G 1)).markedP n⟩

def blockQ (L:Side): Quarry (Long G.ColorIndex) (Co L (PAC G 1)) (fun p=>Slot G (p*L) 1) := { toFull:= (site_eq G).trans (geological L (PAC G 1)).toFull,markedP:= (geological L (PAC G 1)).markedP }
variable {G} {f c : Side}
def motionsQ (x:Long G.ColorIndex) (d:Cover):Long G.ColorIndex:= (((d+x.1.1),x.1.2),x.2)
lemma site_roll (i : Long G.ColorIndex)(d:Cover): (linksQ G).shiftB d i= motionsQ i d:=by rcases i with ⟨⟨x,a⟩,u⟩; unfold motionsQ; dsimp [Quarry.shiftB,linksQ,site_eq]; simp; exact axisEquiv.symm_apply_apply _
lemma strut (i:Long G.ColorIndex)(L:Side)(d:Cover): (blockQ G L).shiftB d i= motionsQ i (L.val • d):=by
 apply (site_eq G).injective
 refine (show site_eq G ((site_eq G).symm ((geological L _).shiftB d (site_eq G i))) = _ from ?_)
 rw [Equiv.apply_symm_apply,c_shift]; rfl
lemma v_loc (i:Long G.ColorIndex) (L n:Side): (blockQ G L).swrap n i=(wrap (n*L) i.1.1,coord i.1.2,i.2):= clamped n L (site_eq G i)
lemma v_coarse (i:Long G.ColorIndex)(n:Side) : (linksQ G).swrap n i=(wrap n i.1.1,coord i.1.2,i.2):=rfl
lemma v_same (i:Long G.ColorIndex)(L n:Side) : (blockQ G L).swrap n i=(linksQ G).swrap (n*L) i:= v_loc ..
variable (H:Layer (Long G.ColorIndex) (Long G.ColorIndex))
lemma block_inv (h:Albedo (linksQ G) (linksQ G) H)(L:Side): Albedo (blockQ G L) (blockQ G L) H:=fun v w x=>by rw [strut,strut,← site_roll,← site_roll];exact h ..
lemma block_periods (h:Albedo (linksQ G) (linksQ G) H)(L p:Side): ledgerRow (blockQ G L) (blockQ G L) H p=ledgerRow (linksQ G) (linksQ G) H (p*L):=by
 let B:=blockQ G L;let S:= linksQ G;ext1 x y;obtain ⟨v,hv⟩:= show ∃ z,B.swrap p z=x from ⟨_,B.both ..⟩; rw [← hv];rw [ledger_at B B _ (block_inv H h L), show B.swrap p v=S.swrap (p*L) v from v_same ..,ledger_at S S H h]; exact congr_arg (fun f=> Stalk.collect f (H v) y) (funext (fun x=> v_same x L p))
end YM.RegulatorIR.Oracle
