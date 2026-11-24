import YM.OPE.Compatible.Dale.Hill
/-!
# Gauge model ordinary finite reps. Orient links from rep to endpoint; readback rotations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Weir
open Function Filter Lattice Laurent Tree Woody Finset
open scoped Topology BigOperators ComplexConjugate Classical
variable {n:Side} (H:Even n.val)
abbrev Node := (sitesK H).Seat
abbrev Limb := (edgesK H).Seat
-- guarantee known typeclass anytime
instance : Fintype (Node H):= by dsimp only [Node,See.Seat]; infer_instance
instance : Fintype (Limb H) := by dsimp only [Limb,See.Seat]; infer_instance
abbrev crumb (x:Site n): Node H := (sitesK H).king x
abbrev pathX (e:edgeV n):Limb H:=(edgesK H).king e
def foot (p:Limb H): Node H:= crumb H p.val.1
def cap (p:Limb H):Node H:= crumb H (p.val.1+step p.val.2)
def dir (e:edgeV n):Bool:=(axisK ((edgesK H).tick e)).flip e.2
@[simp] lemma dir_here (p:Limb H): dir H p.val=false:=by simp only [dir,See.tick_here,axisK_id,Signed.one_flip]
@[simp] lemma path_id (p:Limb H): pathX H p.val=p:=See.king_here ..
@[simp] lemma path_ferry (k:Kv)(e:edgeV n): pathX H (ferry k e)= pathX H e:=See.king_go ..
lemma resettle (e:edgeV n): let p:= pathX H e; let k:= (edgesK H).tick e; e= ferry k p.val:=((edgesK H).ticket e).symm
lemma plunges (k:Kv)(p:Limb H): let e:=p.val; let i:= ferry k e; crumb H i.1= if (axisK k).flip e.2 then cap H p else foot H p:=by
    intro e i; simp only [i,ferry,Step.rotate,Step.used,posDir,Bool.false_xor,axis_pin]; cases h:(axisK k).flip e.2
    · exact (sitesK H).king_go k _
    simp only [↓reduceIte, cap]; let s:=(posDir e.2).rotate (axisK k)
    rw [show decks k e.1-step e.2=decks k (p.val.1+step p.val.2) by rw [← Step.vec_pos (R:=Per n), decks_walk]; change decks _ e.1-step e.2=decks _ e.1+s.vec; simp [s,Step.vec,Step.rotate,posDir,h,sub_eq_add_neg]]; exact (sitesK H).king_go k _
lemma reaches (k:Kv)(p:Limb H): let e:=p.val; let i:= ferry k e; crumb H (i.1+step i.2)= if (axisK k).flip e.2 then foot H p else cap H p:=by
    intro e i; simp only [i,ferry_axis]; simp only [ferry,Step.rotate,Step.used,posDir,Bool.false_xor,axis_pin]; cases h:(axisK k).flip e.2
    · simp only [Bool.false_eq_true,if_false]; rw [show decks k e.1+step e.2=decks k (p.val.1+step p.val.2) from by
         rw [show p.val.1+step p.val.2=e.1+(posDir e.2).vec from rfl,decks_walk]; simp [Step.rotate,Step.vec,posDir,h]]; exact (sitesK H).king_go k _
    simp only [↓reduceIte,sub_add_cancel]; exact (sitesK H).king_go k _
lemma descends (e:edgeV n): let p:= pathX H e; crumb H e.1= if dir H e then cap H p else foot H p := by
    intro p; let k:= (edgesK H).tick e; obtain ⟨hk,hD⟩:e=ferry k p.val ∧ dir H e=(axisK k).flip p.val.2:= ⟨resettle H e,congr_arg ((axisK k).flip) ((congr_arg Prod.snd (resettle H e)).trans (ferry_axis k p.val))⟩; rw [hD]; nth_rw 1 [hk]; exact plunges H k p
lemma finale (e:edgeV n): let p:= pathX H e; crumb H (e.1+step e.2)= if dir H e then foot H p else cap H p := by
    intro p; let k:= (edgesK H).tick e; have he:= resettle H e; change e=ferry k p.val at he; have hv : e.2=p.val.2:=(congr_arg Prod.snd he).trans (ferry_axis ..); unfold dir;change _ = if (axisK k).flip e.2 then _ else _; rw [show (axisK k).flip e.2=(axisK k).flip p.val.2 from congr_arg _ hv]; nth_rw 1 2 [he]; exact reaches H k p
lemma stood (k:Kv)(e:edgeV n): dir H (ferry k e)= ((axisK k).flip e.2).xor (dir H e):=by
     unfold dir; rw [(show (edgesK H).tick (ferry k e)= _ from (edgesK H).tick_go k e), axisK_plus,ferry_axis,Signed.mul_flip,axis_pin]
variable {K:Type*}[Group K]
def coat (t:Limb H→K) : Links (Per n) K:= fun e=> if dir H e then (t (pathX H e))⁻¹ else t (pathX H e)
omit H in def Stores (u:Links (Per n) K):Prop:= ∀ t:Kv,pull (axisK t) (offset t n) u=u
lemma staying (u:Limb H→K): Stores (coat H u):=by
    intro k; funext e; change (if ((posDir e.2).rotate (axisK k)).neg then _ else _)=_; rw [show ((posDir e.2).rotate (axisK k)).neg=(axisK k).flip e.2 from by simp [posDir,Step.rotate]]; change (if (axisK k).flip e.2 then (coat H u (ferry k e))⁻¹ else coat H u (ferry k e))= _; unfold coat; rw [stood,path_ferry]; cases h:(axisK k).flip e.2 <;> cases ht:dir H e <;>simp
lemma rep_coat (u:Limb H→K)(i:Limb H): coat H u i.val=u i:=by simp [coat]
lemma seen_coat (u:Links (Per n) K)(h:Stores u): coat H (fun i=> u i.val)=u:=by
     funext i; let k:= (edgesK H).tick i; let p:= pathX H i; have he: ferry k p.val=i:= (resettle H i).symm; have hh: i.2=p.val.2:= (congr_arg Prod.snd he.symm).trans (ferry_axis ..); have hz := congr_fun (h k) p.val; change (if ((posDir p.val.2).rotate (axisK k)).neg then (u (ferry k p.val))⁻¹ else u (ferry k p.val))=u p.val at hz; rw [show ((posDir p.val.2).rotate (axisK k)).neg=(axisK k).flip p.val.2 from by simp [posDir,Step.rotate],he, ←hh] at hz; change (if (axisK k).flip i.2 then (u p.val)⁻¹ else u p.val)=_; rw [← hz]; cases hy:(axisK k).flip i.2<;>simp
def energyG (t:Node H→K)(u:Limb H→K)(p:Limb H) := t (foot H p)*u p * (t (cap H p))⁻¹
lemma coat_gauge (t:Node H→K)(u:Limb H→K): coat H (energyG H t u)= gauge (fun i=>t (crumb H i)) (coat H u):=by
    funext e; have hf:=descends H e; have hc:=finale H e; unfold coat Lattice.gauge energyG; dsimp only; rw [hc,hf]; cases h:dir H e <;>simp [mul_assoc]
end YM.OPE.Weir
