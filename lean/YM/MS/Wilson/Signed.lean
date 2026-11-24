import YM.MS.Cylinder.Closure
import YM.MS.Wilson.Bare
/-!
# H on stencils across periods

Keep inversion eigenspaces bookkeeping. Proof of Sym action at finite and
 Lens, orientation links at based variables (for Bracket charges).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Orient
open Function Filter Finset Set Plane Koszul Cylinder Lab Taylor Draft Chart Sew Lattice
open Landau
open scoped Topology ContDiff
variable {R : Type} [AddCommGroup R] [One R] {G : Gauge}
local notation "SiteR"=> Four R
abbrev idRail {R:Type}[AddCommGroup R][One R] : Chart.Rail (Four R):= Lattice.step
variable (k: Signed)
def shiftTerm (i:Axis): SiteR:= if k.flip i then -step (k.perm i) else 0
def purse (x:Edge SiteR) : Edge SiteR:= (k.act x.1+shiftTerm k x.2,k.perm x.2)
lemma fst_eq (x:Edge SiteR): (purse k x).1=k.act x.1+(if k.flip x.2 then -step (k.perm x.2) else 0):= rfl
lemma stepflip (v: Axis): k.act (step v:SiteR)=if k.flip v then -step (k.perm v) else step (k.perm v):= by simp_rw [← Step.vec_pos,← Step.vec_rotate]; unfold Step.vec; cases hk:k.flip v <;> simp [Step.rotate,posDir,hk]
lemma purse_d (x:Edge SiteR) : endRail idRail (purse k x)=(if k.flip x.2 then k.act x.1 else k.act (endRail idRail x)):= by unfold purse shiftTerm endRail idRail; rw [Signed.act_add, stepflip]; split <;> simp
lemma purse_base (x:Edge SiteR): (purse k x).1=(if k.flip x.2 then k.act (endRail idRail x) else k.act x.1):= by unfold purse shiftTerm endRail idRail; rw [Signed.act_add,stepflip]; split <;> simp
lemma begL (x:Edge SiteR): purse k⁻¹ (purse k x) = x := by
    refine Prod.ext ?_ ?_
    · rw [purse_base,purse_d]; simp only [purse,Signed.inv_flip,Equiv.symm_apply_apply,shiftTerm]; cases hk:k.flip x.2 <;> simp
    simp [purse]
def wayR (k:Signed): Equiv.Perm (Edge SiteR) where
   toFun:=purse k
   invFun:= purse k⁻¹
   left_inv:=begL k
   right_inv:=fun x=> by simpa using begL k⁻¹ x

def turn (i:LightMode G SiteR) : LightMode G SiteR:= match i with
    | (((none,b),c),x)=>(((none,b),c),k.act x)
    | (((some j,b),c),x)=> (((some (k.perm j),b),c),(purse k (x,j)).1)
lemma reverse_k (i:LightMode G SiteR): turn k⁻¹ (turn k i)=i:= by
    rcases i with ⟨⟨⟨_|j,b⟩,c⟩,x⟩
    · simp [turn]
    have hh := begL k (x,j); simp only [turn,Signed.inv_perm,Equiv.symm_apply_apply]; rw [show ((purse k (x,j)).1,k.perm j)=purse k (x,j) from rfl,hh]
def axise (k:Signed): Equiv.Perm (LightMode G SiteR) where
   toFun:=turn k
   invFun:=turn k⁻¹
   left_inv:=reverse_k k
   right_inv:=fun i=> by simpa using reverse_k k⁻¹ i
lemma commute_pos (x:SiteR)(i: LightMode G SiteR): turn k (post (fun z=>x+z) i)= post (fun z=> k.act x+z) (turn k i):= by
    rcases i with ⟨⟨⟨_|i,b⟩,t⟩,s⟩ <;> simp [turn,purse,post, Signed.act_add,add_assoc]
lemma pos_par (i:LightMode G SiteR): DotFlip (turn k i)=DotFlip i:=by rcases i with ⟨⟨⟨_|i,b⟩,t⟩,s⟩ <;> rfl
lemma turning_project (n:Side) (i:LightMode G Cover): post (wrap n) (turn k i)=turn k (post (wrap n) i):=by
    rcases i with ⟨⟨⟨_|i,b⟩,t⟩,s⟩ <;> simp only [post,turn,wrap_signed] -- step simpl
    simp only [purse,shiftTerm,map_add,wrap_signed]; cases hk:k.flip i <;> simp

-- orientation signs on fields (link)
def fee (x:Option Axis):ℝ:= match x with| none=>1| some j=>cross (k.flip j) true

def σ {P:Type}(i:LightMode G P): ℂ:= fee k i.1.1.1
lemma σ_inv (i:LightMode G SiteR): σ k⁻¹ (turn k i)=σ k i:= by rcases i with ⟨⟨⟨_|i,b⟩,t⟩,s⟩ <;> simp [σ,fee,turn,cross]
def pose : Dot G SiteR→ₗ[ℂ] Dot G SiteR:= (Ferry (turn k)).comp (graffiti (σ k))
lemma pose_s (F H:Dot G SiteR): pose k (couple DotFlip F H)=couple DotFlip (pose k F) (pose k H):= by simp only [pose,LinearMap.comp_apply,tag_grows,ferry_pair (r:=turn k) (fun x=> (pos_par k x).symm)]
lemma pose_t (F:Dot G SiteR)(x:SiteR) : Lab.Shift (k.act x) (pose k F)=pose k (Lab.Shift x F):= by
    unfold pose Lab.Shift transport; simp only [LinearMap.comp_apply,
       ← ferry_rent,show σ k ∘ post (A:=Branch G Axis) (fun z=> x+z) = σ k from rfl,ferry_trans]; congr 2; exact funext fun i=> (commute_pos ..).symm
lemma travel_t (F:Dot G Cover)(n:Side): shown n (pose k F)=pose k (shown n F):= by
    unfold pose shown transport; simp only [LinearMap.comp_apply,← ferry_rent,show σ k ∘ post (A:=Branch G Axis) (wrap n) = σ k from rfl,ferry_trans]; congr 2; exact funext fun i=> turning_project k n i
lemma moving_total [Fintype R](F: Dot G SiteR): sumHome (pose k F)= pose k (sumHome F):= by
    rw [total_uses,total_uses,map_sum, ← Equiv.sum_comp (k.actEquiv (R:=R)).toEquiv] -- equiv add equiv? order
    apply Finset.sum_congr rfl; intro i _; exact pose_t k F i

def stance (F:Dot G Cover):=∀ k:Signed, BulkTest (pose k F) F
end YM.MS.Native.Orient
