import YM.OPE.Compatible.Woods.Moss
/-!
# A Klein four-group action on an auxiliary periodic lattice

`decks` combines axis sign changes with translations by half the period. For an
even side length, `decks_plus` proves the group law. `deck_free` shows that every
nonidentity element moves each site by at least `n.val / 2`, and `pins_axis` gives
a sign change for every axis. These are geometric inputs for controlling zero modes
in position-space estimates. Comparing observables of this auxiliary regulator
with those on the physical torus requires a separate argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Weir
open Function Filter Lattice Laurent Finset
open scoped Topology BigOperators ComplexConjugate
/-! Klein convention -/
structure Kv where
  x : Bool
  y : Bool
deriving DecidableEq
instance : Fintype Kv := Fintype.ofEquiv (Bool × Bool) ⟨fun p=>⟨p.1,p.2⟩,fun k=>(k.x,k.y),fun _=>rfl,fun _=>rfl⟩
lemma kvCard : Fintype.card Kv=4 := by classical
                                          calc
                                           _=Fintype.card (Bool × Bool):= Fintype.card_congr (show Kv ≃ Bool × Bool from ⟨fun k=>(k.x,k.y),fun p=>⟨p.1,p.2⟩,fun _=>rfl,fun _=>rfl⟩)
                                           _=_:=by simp
instance : Zero Kv :=⟨⟨false,false⟩⟩
instance : Add Kv :=⟨fun i j=>⟨i.x.xor j.x,i.y.xor j.y⟩⟩
instance : Neg Kv :=⟨fun k=> k⟩
instance : AddCommGroup Kv where
    add_assoc := by decide
    zero_add := by decide
    add_zero := by decide
    neg_add_cancel := by decide
    add_comm := by decide
    nsmul := nsmulRec; zsmul:= zsmulRec
@[simp] lemma twin (k:Kv): -k=k:=rfl
lemma twinned (k:Kv): k+k=0:= neg_add_cancel k
def axisK (k:Kv) : Signed:=⟨Equiv.refl _,fun i=> if i=0 then k.x else if i=1 then k.y else k.x.xor k.y⟩
def moveK (k:Kv)(i:Axis):Bool:=if i=0 then k.y else if i=3 then false else k.x
@[simp] lemma axis_pin (k:Kv)(i): (axisK k).perm i=i:=rfl
@[simp] lemma axisK_id : axisK 0=1:=Signed.ext rfl (by funext i; simp only [axisK,Signed.one_flip]; split_ifs <;> rfl)
@[simp] lemma axisK_plus (k h:Kv): axisK (k+h)=axisK k*axisK h := Signed.ext rfl (by
    funext i; simp only [Signed.mul_flip,axis_pin]; simp only [axisK]; rcases k with ⟨_|_,_|_⟩ <;> rcases h with ⟨_|_,_|_⟩ <;> split_ifs <;> rfl)
lemma axis_free {k:Kv}(h:k≠0): ∃ i:Axis,(axisK k).flip i=false ∧ moveK k i=true:=by
    rcases k with ⟨_|_,_|_⟩
    · exact (h rfl).elim
    · exact ⟨0,rfl,rfl⟩
    · exact ⟨1,rfl,rfl⟩
    exact ⟨2,rfl,rfl⟩
lemma pins_axis (i:Axis):∃ k:Kv,(axisK k).flip i=true:= by
     by_cases hi:i=1; · exact ⟨⟨false,true⟩, hi ▸ rfl⟩
     exact ⟨⟨true,false⟩, by dsimp [axisK]; simp [hi]⟩
lemma shift_plus (k h:Kv)(i): moveK (k+h) i=(moveK k i).xor (moveK h i):=by unfold moveK; split_ifs<;> rfl
variable {n:Side}
def offset (k:Kv)(n:Side): Site n:=fun i=>if moveK k i then ((n.val/2:ℕ): Per n) else 0
def decks (k:Kv)(x:Site n) := affine (axisK k) (offset k n) x
@[simp] lemma at_nought (n:Side): offset 0 n=0:=by
    funext i; change ite _ _ _=0; rw [if_neg]; unfold moveK; split_ifs <;> decide
@[simp] lemma flats (x:Site n): decks 0 x=x:=by simp [decks,affine]
variable (H:Even n.val)
include H
lemma doubled : ((n.val/2:ℕ):Per n) + ((n.val/2:ℕ):Per n)=0:=by
    obtain ⟨j,hj⟩:=H; rw [← Nat.cast_add,show (n.val/2)+(n.val/2)=n.val by omega]; exact ZMod.natCast_self ..
lemma neg_offset (k: Kv)(i:Axis): -(offset k n i)=offset k n i:=by
   unfold offset; split
   next h=> exact neg_eq_of_add_eq_zero_left (doubled H)
   next h=> simp
lemma act_offset (k h:Kv): (axisK k).act (offset h n)=offset h n:=by
    funext i; change (axisK k).act (offset h n) ((axisK k).perm i)=_; rw [Signed.act_at,neg_offset H]; simp
lemma offset_plus (k h:Kv): offset (k+h) n= offset h n+offset k n:=by
    funext i; simp only [offset,shift_plus,Pi.add_apply]; cases he: moveK k i <;> cases ht:moveK h i <;> simp [← doubled H] 
lemma decks_plus (k h:Kv)(x:Site n): decks (k+h) x=decks k (decks h x):=by
     simp only [decks,affine,axisK_plus, Signed.act_mul,offset_plus H,Signed.act_add,act_offset H]; abel
def roam (k:Kv): Site n ≃ Site n:= ⟨decks k,decks k,fun x=> by rw [← decks_plus H,twinned,flats],fun x=> by rw [← decks_plus H,twinned,flats]⟩
omit H in lemma deck_free (k:Kv)(h:k ≠ 0)(x:Site n) : n.val/2 ≤ separation (decks k x) x := by
     obtain ⟨i,he,hj⟩:= axis_free h
     apply le_trans _ (component_le (decks k x-x) i)
     change _ ≤ (ZMod.valMinAbs ((axisK k).act x ((axisK k).perm i)+offset k n i-x i)).natAbs
     simp only [Signed.act_at, he, Bool.false_eq_true,if_false,offset,hj,if_true,add_sub_cancel_left]; set v:=((n.val/2:ℕ):Per n)
     have hX : ZMod.valMinAbs v=((n.val/2:ℕ):ℤ):= by apply (ZMod.valMinAbs_spec _ _).mpr; refine ⟨by unfold v; rw [Int.cast_natCast],?_⟩; have hr: 0<n.val:= n.pos; change -(n.val:ℤ) < ((n.val/2:ℕ):ℤ)*2 ∧ ((n.val/2:ℕ):ℤ)*2 ≤ (n.val:ℤ); constructor <;> omega
     rw [hX,Int.natAbs_natCast]
omit H in lemma decks_walk (k:Kv)(x:Site n)(d:Step):decks k (x+d.vec)=decks k x+(d.rotate (axisK k)).vec:=by
    rw [Step.vec_rotate]; unfold decks affine; rw [Signed.act_add]; abel
end YM.OPE.Weir
