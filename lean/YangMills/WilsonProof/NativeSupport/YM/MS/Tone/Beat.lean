import YM.MS.Tone.Beat
import YM.MS.Wilson.Splice
import YM.Laurent.Eval
/-!
# Evaluation of incoming momentum planes

Count measures on lattice Brillouin zone. `T'Q` period n family.
   Coordinate symbols Fourier on based for phase; Landau midshift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau
open Momentum Real
open Complex (I)
open scoped Topology ContDiff
def embed (q:Cover) : QP:= fun i=> (q i:ℤ)
variable (p q : QP) (k:Signed)
lemma payadd (r : QP) : bill (p+r) q=bill p q *bill r q:=by
    unfold bill pairing; push_cast; simp [Finset.sum_add_distrib,add_mul,mul_add, Complex.exp_add]
lemma rights (p q:QP): bill p q=bill q p:= by simp only [bill,pairing,mul_comm]
lemma rightadd (x:QP): bill p (q+x)=bill p q *bill p x:=by rw [rights,payadd, rights q p,rights x p]
@[simp] lemma pay0 : bill 0 p=1:= by simp [bill,pairing]
@[simp] lemma right0 : bill p 0=1:= by rw [rights,pay0]
lemma inverse : bill p (-q)= (bill p q)⁻¹:= by simp [bill,pairing,Finset.sum_neg_distrib,Complex.exp_neg]
lemma opp : bill (-p) q= (bill p q)⁻¹:=by rw [rights,inverse,rights q p]
@[simp] lemma nonz : bill p q≠0:= Complex.exp_ne_zero _
lemma bill_norm : ‖bill p q‖=1:= by simp [bill,Complex.norm_exp]
lemma starbill : star (bill p q)=bill (-p) q:= by
    simp [bill,pairing,← Complex.exp_conj,Finset.sum_neg_distrib]
lemma pair_H : pairing (k.act p) (k.act q)=pairing p q:= by
    unfold pairing; rw [← Equiv.sum_comp k.perm]; exact Finset.sum_congr rfl fun i _=> by rw [Signed.act_at,Signed.act_at]; split <;> simp
lemma turnC : bill (k.act p) (k.act q) = bill p q:= by simp only [bill,pair_H]
@[simp] lemma emb_step (u:Axis)(x:Axis): embed (step u) x= if x=u then 1 else 0 := by simp only [embed, step_apply]; split <;> simp
lemma emb_H (k:Signed)(x:Cover): k.act (embed x)=embed (k.act x):= by funext i; obtain ⟨j,rfl⟩:=k.perm.surjective i; rw [Signed.act_at]; unfold embed; rw [Signed.act_at]; split <;> simp
lemma emb_add (x y:Cover): embed (x+y)=embed x+embed y:= by ext; simp [embed]
lemma emb_sub (x y:Cover): embed (x-y)=embed x-embed y:= by ext; simp [embed]
lemma emb_neg (x:Cover): embed (-x)=-embed x:= by ext; simp [embed]
lemma castNative (x:Cover): bill p (embed x)=Laurent.mode (fun i=>(p i:ℂ)) x:=by simp only [bill,Laurent.mode,pairing,embed]; push_cast; rfl

-- mid shift, combine at `atLink`. Leg frame remains vector-shifts.
def offset (a: Atom Axis) : QP:= match a.1 with
    | none=>0
    | some i=> (1/2:ℝ) • embed (step i)
@[simp] lemma here_a (i:Axis)(b:Bool): offset (some i,b)=(1/2:ℝ) • embed (step i):=rfl
@[simp] lemma here_b (b:Bool): offset (none,b)=0:=rfl

def rep : Cover →+ QP where
   toFun x:= (2*π) • embed x
   map_add' x y:= by rw [emb_add,smul_add]
   map_zero':=by ext; simp [embed] -- inspect
lemma reciprocal (x v:Cover): bill (rep x) (embed v)=1:= by
    rw [castNative]; have ht (x:Cover): (fun i=> Complex.ofReal (rep x i))= Laurent.reciprocal x:= by funext i; change (((2*π)*((x i):ℝ):ℝ):ℂ)=_; push_cast; rfl
    rw [ht,Laurent.mode_periodic]
end YM.MS.Tone
