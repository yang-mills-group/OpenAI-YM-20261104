import YM.RegulatorIR.Budget.Packet

/-!
Project by summing over every path lift, anchors chosen legwise. Vacuum tensors
permitted to have a free center -- fix one copy, but any leg convention gives
the same answer. Will need proof of this to avoid volume in connected
contraction estimates. Marked kernels, not assumed inversion-invariant, use
all copies. These lemmas precede gauge Ward use; they are statements on kernel
tensors alone (on the orbit degrees of freedom, symmetrize when needed).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget
open Function Spatial Motion Lattice
open scoped ENNReal NNReal Topology BigOperators Classical

variable {P : ℝ} {X Y U V : Type} {r : ℕ} (A : Deck P X Y)

namespace Deck
open Tuple

def project (x : Tuple X r) : Tuple Y r:= A.orbit ∘ x
def polish (x : Tuple X r) : ℝ := ∏ i,A.orient (x i)
def dyed (T:Packet X r)(x:Tuple X r) := T x * A.polish x
def Ready (T:Packet X r) : Prop:= ∀ d (x:Tuple X r), A.dyed T (A.wind d ∘ x) = A.dyed T x

lemma polish_sq (x:Tuple X r) : A.polish x*A.polish x=1:= by
 unfold polish; rw [← Finset.prod_mul_distrib]; simp_rw [A.sign_sq]; simp
lemma polish_perm (x:Tuple X r)(e:Equiv.Perm (Fin r)): A.polish (x ∘ e)=A.polish x:=Equiv.prod_comp e (A.orient ∘ x)
lemma polish_mov (x:Tuple X r)(d:Motion):A.polish (A.wind d∘x)= d.sign^r * A.polish x := by
 unfold polish; simp [A.retreat,Finset.prod_mul_distrib]
lemma polish_cost (x:Tuple X r) : ‖A.polish x‖ₑ = 1 := by
   unfold polish
   suffices h:∀ s:Finset (Fin r), ‖∏ i∈s,A.orient (x i)‖ₑ=1 by exact h _
   intro s; induction s using Finset.induction_on with
   | empty=>simp
   | insert i s h ih=>rw [Finset.prod_insert h,enorm_mul,A.over_sign,ih,one_mul]
lemma dyed_cost (T:Packet X r)(x:Tuple X r) : ‖A.dyed T x‖ₑ=‖T x‖ₑ:=by rw [dyed,enorm_mul,A.polish_cost,mul_one]
lemma ready_iff (T:Packet X r): A.Ready T ↔ ∀ d (x: Tuple X r), T (A.wind d ∘ x)=d.sign^r * T x:=by
 constructor <;> intro h d x
 · have H := h d x
   unfold dyed at H; rw [A.polish_mov] at H
   let p := d.sign^r; let v:=A.polish x
   have hp : p*p=1:= by unfold p; rw [←mul_pow, Motion.sign_sq,one_pow]
   have hv : v*v=1:= A.polish_sq x
   change _=p* T x
   change _* (p*v)=T x*v at H
   apply mul_right_cancel₀ (mul_ne_zero (left_ne_zero_of_mul (hp.trans_ne one_ne_zero)) (left_ne_zero_of_mul (hv.trans_ne one_ne_zero)) : p*v≠0)
   rw [H,mul_mul_mul_comm,hp, one_mul]
 unfold dyed; rw [A.polish_mov,h,mul_mul_mul_comm,← mul_pow,Motion.sign_sq,one_pow,one_mul]

def scroll (T:Packet X r) : Packet Y r:=Stalk.collect (A.project (r:=r)) (A.dyed T)

/-- `Nest` of lifts with one leg fixed. -/
abbrev Nest (A:Deck P X Y)(q:Tuple Y r)(i:Fin r)(a:X):= {z : Tuple X r // A.project z=q ∧ z i = a}

def lodge (T:Packet X r)(q:Tuple Y r)(i:Fin r)(a:X):ℝ:= ∑' x:Nest A q i a,A.dyed T x.val

section Reroot
-- any choice of lifted root gives the same value, including at another leg
variable (q:Tuple Y r)(i j: Fin r) (a:Stalk A.orbit (q i))(b:Stalk A.orbit (q j))

lemma resites (x:Nest A q i a.val) : ∃! t:Motion,A.wind t (x.val j)= b.val := A.edges _ _ ((congr_fun x.property.1 j).trans b.property.symm)
private def tide (x:Nest A q i a.val): Motion:= Classical.choose (A.resites q i j a b x).exists
private lemma tide_spec (x:Nest A q i a.val): A.wind (tide A q i j a b x) (x.val j)=b.val:= Classical.choose_spec (A.resites q i j a b x).exists
private def towards (x:Nest A q i a.val):Nest A q j b.val := ⟨(A.wind (tide A q i j a b x)) ∘ x.val,funext (fun k=>(A.projected ..).trans (congr_fun x.property.1 k)), tide_spec ..⟩
private lemma from_to (x:Nest A q i a.val): towards A q j i b a (towards A q i j a b x)=x:=by
 let u:= towards A q i j a b x; let w:= A.tide q i j a b x
 have h : A.wind (undo w) (u.val i) = a.val:= by change A.wind _ (A.wind w _)= _; rw [A.reversed, Equiv.symm_apply_apply]; exact x.property.2
 have hE : A.tide q j i b a u = undo w:= (A.resites q j i b a u).unique (A.tide_spec ..) h
 apply Subtype.ext; change A.wind (A.tide q j i b a u) ∘ (A.wind w∘x.val)=x.val; rw [hE,A.reversed]; ext1 k; simp

def transferNest : Nest A q i a.val≃ Nest A q j b.val :=⟨A.towards q i j a b,A.towards q j i b a, from_to A q i j a b,from_to A q j i b a⟩
lemma lodge_here {T:Packet X r}(h:A.Ready T) : A.lodge T q i a.val=A.lodge T q j b.val:=by
 let t := A.transferNest q i j a b
 unfold lodge; rw [← t.tsum_eq]; apply tsum_congr; intro x; exact (h ..).symm
lemma lodge_any {T:Packet X r}(h:A.Ready T){a b:X}(ha:A.orbit a=q i)(hb:A.orbit b=q j):
     A.lodge T q i a=A.lodge T q j b:= A.lodge_here q i j ⟨a,ha⟩ ⟨b,hb⟩ h
end Reroot

/-- On scalars define zero. Used only on extensive tensors treated modulo discarded vacuum. -/
def deckSum (T:Packet X r) : Packet Y r:= fun q=> if h : 0<r then A.lodge T q ⟨0,h⟩ (A.place (q ⟨0,h⟩)) else 0
lemma deck_pivot {T:Packet X r}(h:A.Ready T) (q : Tuple Y r)(i: Fin r)(x)(hh:A.orbit x=q i): A.deckSum T q=A.lodge T q i x:= by rw [deckSum,dif_pos (Fin.pos i)]; exact A.lodge_any q ⟨0,Fin.pos i⟩ i h (A.placed _) hh

section Exact
variable (T : Packet X r)(e : Equiv.Perm (Fin r))
lemma dyed_s (x:Tuple X r) : A.dyed T (Tuple.perm X e x)= A.dyed (T ∘ Tuple.perm X e) x:= by unfold dyed; rw [show Tuple.perm X e x= x ∘ e from rfl, A.polish_perm]; rfl
lemma dyed_sym (h:Packet.IsSym T) (x : Tuple X r) : A.dyed T (x ∘ e)= A.dyed T x:= by unfold dyed; rw [h e,A.polish_perm]
lemma dyed_perm (h:A.Ready T) : A.Ready (T ∘ Tuple.perm X e) := by intro d z; rw [← A.dyed_s, ← A.dyed_s]; exact h d (z ∘ e)
lemma scroll_perm x : A.scroll (T ∘ Tuple.perm X e) x=A.scroll T (Tuple.perm Y e x) := by
 let W : Stalk A.project x ≃ Stalk A.project (Tuple.perm Y e x):= Equiv.subtypeEquiv (Tuple.perm X e) (fun a=>⟨(fun h=> show A.project _ = _ from congr_arg (Tuple.perm Y e) h),fun h=>(Tuple.perm Y e).injective h⟩)
 unfold scroll Stalk.collect; rw [← W.tsum_eq]; apply tsum_congr;intro b; exact (A.dyed_s ..).symm
lemma deck_perm (h:A.Ready T) x : A.deckSum (T ∘ Tuple.perm X e) x=A.deckSum T (Tuple.perm Y e x):=by
 unfold deckSum; split 
 next hr =>
   let i:Fin r:=⟨0,hr⟩
   let a:= A.place (x (e i))
   let W:Nest A x (e i) a ≃ Nest A (Tuple.perm Y e x) i a:= Equiv.subtypeEquiv (Tuple.perm X e) (fun z=> by
       constructor
       · intro ⟨h,h'⟩; exact ⟨congr_arg (Tuple.perm Y e) h,h'⟩
       intro ⟨h,h'⟩; exact ⟨(Tuple.perm Y e).injective h,h'⟩)
   rw [A.lodge_any x i (e i) (A.dyed_perm T e h) (A.placed _) (A.placed _)]
   unfold lodge
   change _ = ∑' b : Nest A (Tuple.perm Y e x) i a, _
   rw [← W.tsum_eq]; apply tsum_congr;intro b; exact (A.dyed_s ..).symm
 rfl
end Exact

/-- All projected tuples with the index `i` held at an orbit value, summed using
the same lift `x`. -/
def projectedHold (i:Fin r)(x:X): Hold i x → Hold i (A.orbit x) :=
 fun a=>⟨A.project a.val, congr_arg _ a.property⟩
private def rooms (i:Fin r)(x:X)(p:Hold i (A.orbit x)) : Nest A p.val i x ≃ Stalk (A.projectedHold i x) p where
 toFun a:=⟨⟨a.val,a.property.2⟩,Subtype.ext a.property.1⟩
 invFun b:=⟨b.val.val, by exact ⟨Subtype.ext_iff.mp b.property,b.val.property⟩⟩
 left_inv a:= rfl
 right_inv b:= rfl
lemma parcel (T:Packet X r)(i:Fin r)(x:X)(p:Hold i (A.orbit x)): A.lodge T p.val i x = Stalk.collect (A.projectedHold i x) ((A.dyed T) ∘ Subtype.val) p:= (A.rooms i x p).tsum_eq (fun v=>A.dyed T v.val.val)

lemma parcel_quota (f:Tuple X r→ℝ≥0∞)(i:Fin r)(x:X):
   (∑' p: Hold i (A.orbit x), ∑' v : Nest A p.val i x, f v.val)=∑' v: Hold i x, f v.val:= by
 refine (tsum_congr (g:=fun p=>∑' v : Stalk (A.projectedHold i x) p, f v.val.val) fun p=>?_).trans ?_
 · exact (A.rooms i x p).tsum_eq (fun v=> f v.val.val)
 exact ENNReal.tsum_fiberwise (fun v => f v.val) (A.projectedHold i x)

section Cost
-- restriction of diameter/anchor
variable {l : ℝ} (hp:0<P)(hl:0<l)(u:ℕ)
local notation "F" => Tariff.onFold P hp l hl u
local notation "G" => Tariff.native l hl u
lemma equiv_width (x:Tuple X r) : ((F).uses A.atO).diameter (A.project x)=((F).uses A.pos).diameter x:=by
 have h (p q:Fin r) : ((F).uses A.atO).road (A.project x p) (A.project x q) = ((F).uses A.pos).road (x p) (x q):=congr_arg (Tariff.amount l u) (A.d_tile A hp ..)
 unfold Tariff.diameter; simp_rw [h]
lemma cheap_d (x y : X): ((F).uses A.atO).road (A.orbit x) (A.orbit y) ≤ ((G).uses A.pos).road x y := by
 apply Tariff.amount_mono hl
 rw [A.d_tile _ hp]; exact (distance_le hp _ _ (across 0)).trans_eq (by rw [Motion.neutral_loc])
lemma cheap_mark (z)(x: Tuple X r): ((Premium.rooted F z).uses A.atO).width (A.project x) ≤ ((Premium.rooted G z).uses A.pos).width x:=by
 let T := (Premium.rooted G z).uses A.pos
 apply Premium.width_le
 · refine le_trans (Tariff.diameter_le _ (((G).uses A.pos).diameter_unit x) fun p q=> le_trans (A.cheap_d hp hl u ..) (((G).uses A.pos).diameter_ge x p q)) (T.width_diameter x)
 intro i; apply le_trans _ (T.width_ge x i); change Tariff.amount _ _ (distance P z _)≤ Tariff.amount _ _ (dist z _)
 rw [show A.project x i=A.orbit (x i) from rfl,A.x_tile hp]; exact Tariff.amount_mono hl _ ((Spatial.distance_le hp _ _ (Motion.across 0)).trans_eq (by rw [Motion.neutral_loc]))
lemma scroll_bound (z)(T : Packet X r): Packet.markQ ((Premium.rooted F z).uses A.atO) (A.scroll T)≤ Packet.markQ ((Premium.rooted G z).uses A.pos) T :=
 (Stalk.quota_collect A.project (A.dyed T) _).trans ((quota_mono _ (fun x=>A.cheap_mark hp hl u z x)).trans (quota_eq _ _ _ (A.dyed_cost T)).le)
lemma deck_local (T:Packet X r)(h:A.Ready T){c:ℝ≥0∞}(hi:Packet.localQ ((G).uses A.pos) T c): Packet.localQ ((F).uses A.atO) (A.deckSum T) c:=by
 intro i y
 obtain ⟨x,rfl⟩ : ∃ x,A.orbit x=y:=⟨_,A.placed y⟩
 let t:=A.projectedHold i x
 let f (b:Hold i x):= A.dyed T b.val
 have he (p:Hold i (A.orbit x)): A.deckSum T p.val=Stalk.collect t f p:= (A.deck_pivot h p.val i x p.property.symm).trans (A.parcel T i x p)
 unfold Stalk.scopeQ; rw [funext he]
 apply (Stalk.quota_collect t f _).trans
 unfold f
 rw [quota_eq _ (fun v:Hold i x=> T v.val) _ (fun v=>A.dyed_cost ..)]
 apply (quota_mono (fun v:Hold i x=> T v.val) ?_).trans (hi i x)
 intro a; change ((F).uses A.atO).diameter (A.project a.val) ≤ _
 exact Tariff.diameter_le _ (((G).uses A.pos).diameter_unit a.val) fun p q=>le_trans (A.cheap_d hp hl u ..) (((G).uses A.pos).diameter_ge a.val p q)

end Cost
end Deck
end YM.RegulatorIR.Budget
