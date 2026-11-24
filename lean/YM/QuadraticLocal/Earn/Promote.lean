import YM.QuadraticLocal.Earn.Club
import YM.QuadraticLocal.Echo.Spot
/-! # Packaging the mask support and actual walks of a received analytic row

 Before any budget on reading it in the *real layout*, retain the inherited winding and
 analytic address costs in the assembled stencil. Attach each actual marker root and
 its inherited addresses, not just "coarse Owner first" of the cover kernel. Lights
 acknowledge projection ancestry before imposing aperture budget.

 On both short and long (possibly winding) cover outputs, root tags from EVERY member
 included at the actual connector **via the owning cover slot in this Lantern**.
 At subsidiary roots from a given wing, use those offsets and then one compressed walk
 pricing the old length. Subscriber may keep old visits too for requesting stricter predicates,
 but on root hull re-expression keep these obligatory costs. At fixed volume old windings
 just identified at projected sites stay charged using the inherited lengths, with the
 displayed `surcharge`. This doesn't assert short-output supports in the aligned log,
 use the syllabus gates for that subcase.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ} {k u i' h : ℕ}
variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)
namespace Promote
open Cable Club
variable (Y: Poetry.Lantern G (Club.Keys X C))
set_option quotPrecheck false
local notation "K"=> Club.Keys X C
local notation "O"=> Club.lowest X C
local notation "Θ"=> Club.alliance X C
local notation "p'"=> Club.roof X C q
local notation "S"=> Club.site X C q
local notation "L"=> q.count.val
local notation "M"=> (P.coarser q)
local notation "V₁"=> Club.troops X C
local notation "Φ"=> Club.stamp X C
local notation "Ψ"=> Club.joint X C
local notation "Fp"=> P.origin
variable (H:Y.Bears Finset.univ (Club.lowest X C) h)(E:Echo.Spot.Entails Y (Club.lowest X C) (Club.site X C q))
-- canonical route with THAT true length. inherited test frames inclusive.P_slot
namespace Route
def climb (y:Cover):= route 0 y 1
@[simp] lemma len (y:Cover): (Route.climb y).length=Laurent.size y:=by
   apply Nat.add_right_cancel (m:=4) -- naming wrong
   exact PriceCompiler.Canonical.sizeSlot ⟨(0,1), by decide⟩ y
lemma atStop (x:Site c)(y:Cover): stop x (climb y) = x+ wrap c y:=by unfold climb; nth_rw 1 [show x=x+wrap c 0 from by simp]; rw [Work.E03.stop_add_left,← wrap_stop_cover,route_end]
lemma projected_length (x:Site c)(y:Cover): separation x (x+ wrap c y) ≤ Laurent.size y:=by rw [← Route.len,← Route.atStop]; exact Paths.to_ball _ _ (Native.tip ..)
end Route

def receipt (i:Club.Keys X C):Cover:= Classical.choose (Spot.owns Y (Club.lowest X C) H i)
local notation "U"=> receipt X C Y H
include H
lemma belongs (i:K) : (U i,i)∈Y.roots:= Classical.choose_spec (Spot.owns Y _ H i)
lemma ties (i:K): Laurent.size (U i) ≤ Y.length:=by
   have ht: Laurent.size (U i) ≤ Ink.meter Y.roots:= List.le_sum_of_mem (List.mem_map.mpr ⟨(U i,i),belongs X C Y H i,rfl⟩)
   exact ht.trans (Nat.le_add_right ..)

include E
lemma label (i:K): S i= p'+wrap c (U i):= E (U i,i) (belongs X C Y H i)
lemma tethered : Club.reach X C q ≤ Y.length:=by
    apply Club.extent_le X C q
    intro i hi; obtain ⟨j,rfl⟩:= Club.attends_rev X C i hi; let t:=p'; have he : separation t (S j) ≤ Laurent.size (U j):=by rw [Promote.label X C q Y H E]; exact Route.projected_length ..
    exact he.trans (ties X C Y H ..)
omit E H

def front : V:= (V₁ O).binder.front

def draft (i:Club.Keys X C)(v:V): Walk := Cable.follows q ((V₁ i).center) ((V₁ i).binder.path v)

def direct (v:V) := Route.climb (U (Ψ v)) ++ draft X C q (Ψ v) v

def surcharge := Y.length + ∑ i∈ C.val,Cable.mass q ((X i).length)

def mend : Binder (P.coarser q) R where
   mode := Club.alliance X C
   front := front X C
   east := Club.earn X C (Φ O) (Club.attends ..) ((V₁ O).binder.east)
   path := direct X C q Y H
   span v hv:= by rw [direct,stop_append,Route.atStop,show (P.coarser q).origin (front X C) = p' from rfl, ← label X C q Y H E];
                    let i:= Ψ v; let w:= (V₁ i).binder.path v; change stop (q.parent (V₁ i).center) (Cable.follows q (V₁ i).center w)=q.parent (P.origin v); rw [Cable.follows_tip]; exact congr_arg q.parent ((V₁ i).binder.capacity v (Club.join_rank X C hv))
   extra := surcharge X C q Y
local notation "w_0"=> (mend X C q Y H E)

include H E
-- length bound per v, may use `C.reach` for eligibility in addition
lemma oneVisit (v:V)(hv:v∈ (Θ).val) : (w_0).distance v ≤ Y.length + 2 * Cable.mass q (V₁ (Ψ v)).length := by
   let i:= Ψ v; let x:= V₁ i; have ht:= x.binder.dues v (Club.join_rank X C hv); let a:= x.binder.path v; let y:= (P.height v); have he: a.length + y ≤ x.length:= ht.trans (Nat.le_add_right ..);
   unfold Binder.distance mend direct draft; dsimp only [List.length_append, Passport.coarser]
   change _ + Cable.mass q y ≤ _
   rw [List.length_append, Route.len, two_mul]; exact (Nat.add_le_add (Nat.add_le_add (ties X C Y H i) ((Cable.follows_bound q x.center a).trans (Cable.mass_mono q ((Nat.le_add_right a.length _).trans he)))) (Cable.mass_mono q ((Nat.le_add_left y _).trans he))).trans_eq (Nat.add_assoc ..)
local notation "ln"=> Club.length X C
local notation "V0"=> (Cable.mass q ln)
lemma bounds (hm:(Club.alliance X C).val.card≤k) : (w_0).length+Y.atom.length ≤ (k+2)*Y.length+3*k*V0:=by
   let s:= Θ; let p:= Y.length; let t:= V0; have he(i:V)(hi:i∈(s).val):(w_0).distance i ≤ p+2*t:= (oneVisit X C q Y H E i hi).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Cable.mass_mono q (Club.en_route X C _ (Club.attends ..)))) _)
   have ht : ∑ i∈(s).val,(w_0).distance i ≤ k*(p+2*t):= (Finset.sum_le_sum he).trans (by rw [Finset.sum_const, nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hm)
   have hp:surcharge X C q Y ≤ p+k*t := Nat.add_le_add_left ((Finset.sum_le_sum (s:=C.val) (g:=fun _=> t) (fun i hi=> Cable.mass_mono q (Club.en_route X C i hi))).trans (by rw [Finset.sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ ((Club.cardLe X C).trans hm))) _
   have hz:Y.atom.length≤p:=Nat.le_add_left ..; unfold Binder.length; change surcharge X C q Y+(∑ i∈(s).val,_)+_≤_; nlinarith only [ht,hp,hz]
end Promote
end YM.QuadraticLocal.Earn
