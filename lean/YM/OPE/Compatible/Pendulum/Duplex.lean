import YM.OPE.Compatible.Royal.Quilt
import YM.OPE.Compatible.Portage.Market
/-!
# Tilt by one moving center (without assuming it's a lattice origin at the parent clock).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder
open Station
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X]
   {G:Gauge}(C:Family G)(p J k N b i :ℕ)
-- principal Root index true. new S-cohort FALSE
local notation "B"=> Site (C.side J p)
local notation "D"=> B × Bool
local notation "E"=> Mix.camp C p J
def intoSky (b:Bool) : (Site (C.side J p)) ↪ D:= ⟨fun x=>(x,b),fun _ _ h=> congr_arg Prod.fst h⟩
def clouds : Ensemble (Site (C.side J p) × Bool):=
   ⟨(0,true), hands C p J ∘ Prod.fst,fun i=>Equiv.swap (0,true) i, fun _=> Equiv.swap_apply_left ..,P_on ..⟩
lemma registerCloud : Screenlet (listP C p J) (clouds C p J) (intoSky C p J true):=by
   refine ⟨rfl,rfl,fun i=>?_⟩; funext v; change Equiv.swap ((0:B),true) (i,true) (v,true)= (Equiv.swap 0 i v,true); by_cases hv:v=0; · simp [hv]
   by_cases ht:v=i; · rw [ht]; simp
   rw [Equiv.swap_apply_of_ne_of_ne (by simpa) (by simpa),Equiv.swap_apply_of_ne_of_ne hv ht] -- simp using hv
variable (x y:Site (C.side N p))
def rootTilt : Track C.path D p:= fun j v=>if v.2 then Mix.camp C p J j v.1 else axis C p N J (-x) j v.1
def signBase (s:Bool):= if s then y else y-x
def board : Track C.path D p:= fun j v=> axis C p N J (signBase C p N x y v.2) j v.1
set_option quotPrecheck false
local notation "T!"=> rootTilt C p J N x
lemma tilt_moves (h:J ≤ k)(hk:k ≤ N)(w: Site (C.side k p))(ht:x =(C.S.toDepth hk p).embed w):Migrating C.path k p N (rootTilt C p J N x):=by
   let T:= C.S.toDepth hk p; have hv:-x=T.embed (-w):=by rw [ht]; exact (T.root.map_neg ..).symm
   refine ⟨fun j hJ hN=> funext fun ⟨z,b⟩=>?_⟩; cases b
   · dsimp only [Function.comp_apply,rootTilt]; simp only [Bool.false_eq_true,↓reduceIte,hv]; exact congr_fun ((reel C p N J h hk (-w)).mare _ hJ hN) z
   dsimp only [Function.comp_apply,rootTilt]; simp only [ite_true]; exact congr_fun ((uphill C J k p N h).mare _ hJ hN) z
private lemma loops_sub (hk:i≤N)(T:Site (C.side i p))(ht:x=(C.S.toDepth hk p).embed T):
    loops C N p (y-x) i= loops C N p y i + loops C N p (-x) i:=by
    let R:=C.S.toDepth hk p; have hv:-x=R.embed (-T):=by rw [ht]; exact (R.root.map_neg ..).symm
    rw [Ribbons.vote C N p i _ hk,Ribbons.vote C N p i _ hk,Ribbons.vote C N p i _ hk,sub_eq_add_neg,hv]; change R.parent (y+R.embed (-T))=R.parent y+R.parent (R.embed (-T)); rw [R.embed_parent]; simpa [affine] using parent_affine R (C.S.toDepth_odd ..) 1 (-T) y
lemma board_move (h:J ≤ i)(hI:i ≤ N)(w:Site (C.side i p))(ht:x=(C.S.toDepth hI p).embed w)(a:Site (C.side J p)×Bool):
   board C p J N x y i a= affine ((clouds C p J).move a).1 (T! i a) (board C p J N x y i (clouds C p J).v):=by
   rcases a with ⟨a,b⟩; unfold board signBase rootTilt axis clouds; cases b
   next =>
      dsimp only; simp only [Bool.false_eq_true,↓reduceIte]; rw [biteT C J N p i _ h]; unfold bites; simp only [ite_true]; rw [loops_sub C p N i x y hI _ ht,affine, Signed.act_add]; simp only [Function.comp_apply,affine,add_assoc] -- orientation N i ordering
   next =>
      dsimp only; simp only [ite_true]; exact bit C J N p i y h a true
lemma tilted {s:ℕ}(he:s ≤ k)(hx:s ≤ N)(hi:k ≤ N) (W:Site (C.side s p))(hr:x=(C.S.toDepth hx p).embed W) : ∃ T:Site (C.side k p), x=(C.S.toDepth hi p).embed T := ⟨(C.S.toDepth he p).embed W,hr.trans (embed_comp ..)⟩
end YM.OPE.Arboreal.Pixel
