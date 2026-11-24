import YM.XSpace.Influence
import YM.XSpace.Closet
import YM.XSpace.Twins

/-!
# Real-Euclidean equator through the free scheme arrays

Fields = elements of the filtered Wick space. `Change` = linearization
of the whole frame group through any finite horizon, not a chosen subgroup.
Positions tested on the physical fields, so these changes are complex-linear
and commute with real involution (compatible with actual Ref/Table etc conventions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n :ℕ}


def project (d:ℕ): WickPol G→ₗ[ℂ] Sec G d:= (coeS d).leftInverse
lemma seated (p:Sec G d): project d p.val=p:= by change project _ (coeS _ p)=p; exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr Subtype.val_injective) _
def reelR (d:ℕ): Module.End ℝ (Sec G d):={ toFun:= reel d, map_add':=map_add _, map_smul':=fun a x=> reel_scale x a }
lemma real_tests {X Y : Sec G d→ₗ[ℂ] WickPol G} (H:∀ x, reel d x=x→ X x=Y x): X=Y:=by
  apply LinearMap.ext; intro p; let q:= reel d p; let U:=p+q; let V:=Complex.I • p
  have hu := H U (show reel d U=U from by simp only [U,map_add,q,reel_back]; abel)
  have hv := H (V+reel d V) (by rw [map_add,reel_back,add_comm])
  unfold U q at *; simp only [map_add] at hu hv; unfold V at hv; simp only [(reel d).map_smulₛₗ,map_smul] at hv; rw [show (starRingEnd ℂ) Complex.I= -Complex.I by simp] at hv; apply smul_right_injective (WickPol G) (by norm_num : (2:ℂ)≠0)
  have hh: X p - X (reel d p)= Y p-Y (reel d p):= smul_right_injective (WickPol G) Complex.I_ne_zero (show Complex.I • _= Complex.I • _ from by rw [smul_sub,smul_sub]; simpa [neg_smul, sub_eq_add_neg] using hv)
  -- add equations
  change (2:ℂ) • X p= (2:ℂ) • Y p; simp only [two_smul]; exact (show X p+X p=X p-X (reel d p)+(X p+X (reel d p)) by abel).trans (by rw [hh,hu]; abel)


def spill (T:Module.End ℂ (Sec G d)): Module.End ℂ (WickPol G):= (coeS d).comp (T.comp (project d))
lemma swept (T:Module.End ℂ (Sec G d)) (p:Sec G d): spill T p.val=(T p).val:= by change coeS d (T (project d p.val))=_; rw [seated]; rfl
lemma Change_in (T:Change G d) {l} (hl:l≤d) (p:WickPol G) (h:p∈shellSector G l): spill T.val p∈shellSector G l:=by
  let P:Sec G d:=⟨p,chain hl h⟩; rw [show spill T.val p=(T.val P).val from swept T.val P]; exact T.property.2.1 l hl P h
lemma Change_oriented (T:Change G d): Equivariant d (spill T.val):=by
  intro s p h; let P:Sec G d:=⟨p,h⟩; change spill T.val (reflectPol s.ortho P.val)= reflectPol s.ortho (spill T.val P.val); rw [← val_ori,swept,swept, T.property.2.2.2 s, val_ori]
lemma Change_unit (T:Change G d): spill T.val 1=0:=by change spill T.val (leaf G d).val=0; rw [swept,T.property.1]; rfl

def scene (x:Points n) (d:ℕ):= (moment G x).compLinearMap (fun _=> coeS d)
lemma screen (x:Points n) (p: Fin n→ Sec G d): scene x d p = moment G x (fun i=>(p i).val):=rfl
lemma whir (x:Points n) (p:Fin n→Sec G d) (i:Fin n) (T:Module.End ℂ (Sec G d)): scene x d (update p i (T (p i)))= moment G x (update (fun j=>(p j).val) i (spill T (p i).val)):=by
  rw [screen,swept]; apply congr_arg; funext j; by_cases hi:j=i <;> simp [hi]
lemma genre (T:Change G d) : silence G d (spill T.val) ↔ ∀ n (x:Points n), x∈conf n→∀ v:Fin n→Sec G d,∑ i, scene x d (update v i (T.val (v i)))=0:=by
  constructor
  · intro ht n x hx v; simp_rw [whir]; exact ht n _ x (fun i=>(v i).property) hx
  intro h n p x hp hx; let g (i:Fin n):Sec G d:=⟨p i,hp i⟩; have he:=h n x hx g; simp_rw [whir] at he; exact he
end YM.XSpace.Normalize
