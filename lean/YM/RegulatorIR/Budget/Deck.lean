import YM.RegulatorIR.Budget.Sums

/-!
Orbit and native-cover labels and sign conventions. Abstraction includes
periodic shift and tensor inversion; assumes *free action on these labels*
(positive links with even side). Not a rule for winding sums on the
sector of vacuum densities not attached to a leg. The `Layer` operations
project linear substitution kernels and contraction covariances -- the same
bookkeeping applies to either, not the physics that produces them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget

open Function Spatial Motion Lattice
open scoped ENNReal NNReal Topology BigOperators Classical

structure Deck (P : ℝ) (I O : Type) where
  pos : I→Room
  orbit : I→O
  place : O→I
  placed a : orbit (place a)=a
  wind : Motion→ Equiv.Perm I
  neutral a : wind (across 0) a=a
  reversed d : wind (undo d)=(wind d).symm
  projected d a : orbit (wind d a)=orbit a
  displaced d a : pos (wind d a)=loc P d (pos a)
  edges a b : orbit a=orbit b → ∃! d : Motion, wind d a=b
  orient : I → ℝ
  north x : orient (place x)=1
  retreat d x : orient (wind d x) = sign d*orient x

variable {P : ℝ} {X Y U V : Type}

namespace Deck

lemma over_sign (A : Deck P X Y) (x) : ‖A.orient x‖ₑ = 1 := by
  obtain ⟨d,h,-⟩:= A.edges (A.place (A.orbit x)) x (A.placed _)
  rw [← show A.wind d (A.place (A.orbit x))=x from h,A.retreat,A.north,mul_one]
  cases d <;> simp [Motion.sign]
lemma sign_sq (A : Deck P X Y) x : A.orient x * A.orient x=1:=by
  obtain ⟨d,h,-⟩:= A.edges (A.place (A.orbit x)) x (A.placed _)
  rw [← h,A.retreat,A.north,mul_one]; exact Motion.sign_sq _

def atO (A:Deck P X Y)(x:Y):= A.pos (A.place x)
variable (A:Deck P X U)(B:Deck P Y V)
lemma d_tile (hp:0<P) (x y):
    distance P (A.atO (A.orbit x)) (B.atO (B.orbit y))=distance P (A.pos x) (B.pos y):=by
 obtain ⟨u,h,-⟩:= A.edges x (A.place (A.orbit x)) (A.placed _).symm
 obtain ⟨v,s,-⟩:= B.edges y (B.place (B.orbit y)) (B.placed _).symm
 rw [Deck.atO,Deck.atO,←h,←s,A.displaced,B.displaced,distance_deck hp,distance_comm hp,distance_deck hp,distance_comm hp]
lemma s_tile (hp:0<P) (x): singular P (A.atO (A.orbit x))=singular P (A.pos x):=by
 obtain ⟨u,h,-⟩:= A.edges x (A.place (A.orbit x)) (A.placed _).symm
 rw [Deck.atO,←h,A.displaced,singular_deck hp]
lemma x_tile (hp:0<P) (x) (a): distance P a (A.atO (A.orbit x))=distance P a (A.pos x):=by
 obtain ⟨u,h,-⟩:= A.edges x (A.place (A.orbit x)) (A.placed _).symm
 rw [Deck.atO,←h,A.displaced,distance_deck hp]
lemma remote (hp:0<P) {x y} (h:A.orbit x=A.orbit y)(hh:x≠y): singular P (A.pos x) ≤ dist (A.pos x) (A.pos y):=by
 obtain ⟨u,hv,-⟩:= A.edges x y h
 rw [←hv,A.displaced]; refine holonomy hp _ (fun he=>hh ?_); rw [he,A.neutral] at hv; exact hv
def catalog (u:U) : Motion ≃ Stalk A.orbit u := by
 refine Equiv.ofBijective (fun d:Motion=> ⟨A.wind d (A.place u), by rw [A.projected, A.placed]⟩) ⟨fun d e he=>?_,?_⟩
 · have h:A.wind d (A.place u)=A.wind e (A.place u):= Subtype.mk.inj he
   exact (A.edges _ _ (A.projected d (A.place u)).symm).unique rfl h.symm
 rintro ⟨v,hv⟩
 obtain ⟨w,h,-⟩:= A.edges (A.place u) v ((A.placed u).trans hv.symm)
 exact ⟨w,Subtype.ext h⟩
@[simp] lemma catalog_place (u:U) (d:Motion) : (A.catalog u d).val = A.wind d (A.place u):= rfl

end Deck

abbrev Layer (X Y : Type):= X→Y→ℝ

namespace Layer
variable {Z : Type}
def row (F : Layer X Y)(A:Tariff Z)(x:X→Z)(y:Y→Z)(c:ℝ≥0∞): Prop:=
  ∀ i, quota (F i) (fun j=>A.road (x i) (y j)) ≤ c
def height (F : Layer X Y)(c:ℝ≥0∞): Prop:= ∀ x y, ‖F x y‖ₑ ≤ c
lemma row_pointer {F : Layer X Y}{A:Tariff Z}{x:X→Z}{y:Y→Z}{c:ℝ≥0∞}(h:row F A x y c)(i:X)(j:Y) : ‖F i j‖ₑ * A.road (x i) (y j) ≤ c := (term_le ..).trans (h i)
lemma row_to_sup {F : Layer X Y}{A:Tariff Z}{x:X→Z}{y:Y→Z}{c:ℝ≥0∞}(h:row F A x y c): height F c := by
 intro i j; exact le_trans (by nth_rw 1 [← mul_one ‖F i j‖ₑ];exact mul_le_mul_right (A.unit (x i) (y j)) _) (row_pointer h i j)
lemma row_mono {F : Layer X Y}{A B:Tariff Z}{x:X→Z}{y:Y→Z}{c:ℝ≥0∞} (h:∀ i j,B.road i j ≤ A.road i j) (hh:row F A x y c): row F B x y c :=
 fun _=>(quota_mono _ fun _=>h _ _).trans (hh _)
lemma row_fold (P:ℝ) (hp:0<P) {l : ℝ} (hl:0<l) (a:ℕ) {A:Deck P X U}{B:Deck P Y V}{F : Layer X Y}{c:ℝ≥0∞}
    (hh:row F (Tariff.native l hl a) A.pos B.pos c):row F (Tariff.onFold P hp l hl a) A.pos B.pos c :=
 row_mono (A:=Tariff.native l hl a) (fun x y=> Tariff.amount_mono hl a ((Spatial.distance_le hp x y (Motion.across 0)).trans_eq (show dist x (loc P (across 0) y) = dist x y by rw [Motion.neutral_loc]))) hh

def Sym (A:Deck P X U) (B:Deck P Y V)(F:Layer X Y):Prop:=∀ d x y,F (A.wind d x) (B.wind d y)= F x y
variable (A:Deck P X U)(B:Deck P Y V)(F:Layer X Y)

def paint (x)(y):= F x y * (A.orient x * B.orient y)
lemma painted (h: Sym A B F)(x y d): paint A B F (A.wind d x) (B.wind d y)=paint A B F x y :=by
 unfold paint; rw [h,A.retreat,B.retreat,mul_mul_mul_comm,Motion.sign_sq, one_mul]
lemma shade x y : ‖paint A B F x y‖ₑ=‖F x y‖ₑ:=by unfold paint; rw [enorm_mul,enorm_mul,A.over_sign,B.over_sign,one_mul,mul_one]

def forwardCost (x)(y:V):= Stalk.collect B.orbit (paint A B F x) y
def wrapL (u v):= forwardCost A B F (A.place u) v
lemma from_proj (h:Sym A B F)(x: X)(y:V) : forwardCost A B F x y=wrapL A B F (A.orbit x) y:= by
 obtain ⟨d,he,-⟩:= A.edges x (A.place (A.orbit x)) (A.placed _).symm
 let E : Stalk B.orbit y≃Stalk B.orbit y:= Equiv.subtypeEquiv (B.wind d) fun _=> by rw [B.projected]
 unfold wrapL forwardCost Stalk.collect
 calc
  _ = ∑' v : Stalk B.orbit y,paint A B F (A.place (A.orbit x)) (E v).val := by apply tsum_congr; intro b; rw [←he]; exact (painted A B F h x b.val d).symm
  _ = _:= E.tsum_eq (fun v=>paint A B F (A.place (A.orbit x)) v.val)
lemma other (h:Sym A B F)(u: U)(v: V) : wrapL A B F u v=wrapL B A (Function.swap F) v u := by
 unfold wrapL forwardCost Stalk.collect
 let G:Motion≃Motion:= ⟨undo,undo,undo_undo,undo_undo⟩
 rw [← (B.catalog v).tsum_eq (fun i=>paint A B F (A.place u) i.val),
     ← (G.trans (A.catalog u)).tsum_eq (fun i=>paint B A (Function.swap F) (B.place v) i.val)]
 apply tsum_congr
 intro d
 simp only [Deck.catalog_place,Equiv.trans_apply]
 change paint A B F (A.place u) (B.wind d (B.place v))=paint B A (Function.swap F) (B.place v) (A.wind (undo d) (A.place u))
 nth_rw 1 [← painted A B F h _ _ (undo d),B.reversed,Equiv.symm_apply_apply]
 unfold paint Function.swap; rw [mul_comm (A.orient _)]

lemma row_cost {l:ℝ} {b:ℝ≥0∞}(hp:0<P)(hl:0<l)(a:ℕ)(hh: row F (Tariff.native l hl a) A.pos B.pos b):
  row (wrapL A B F) (Tariff.onFold P hp l hl a) A.atO B.atO b:=by
 intro x
 let T:=Tariff.onFold P hp l hl a
 refine le_trans (Stalk.quota_collect B.orbit (paint A B F (A.place x)) (fun j=>T.road (A.atO x) (B.atO j))) ?_
 rw [quota_eq _ (F (A.place x)) _ (fun i=> shade A B F (A.place x) i)]
 apply (quota_mono (F (A.place x)) ?_).trans (row_fold P hp hl a (A:=A) (B:=B) hh (A.place x))
 intro y
 exact le_of_eq (congr_arg (Tariff.amount l a) (show distance P (A.atO x) (B.atO (B.orbit y))=distance P (A.pos (A.place x)) (B.pos y) from
    (by simpa only [A.placed] using A.d_tile B hp (A.place x) y)))

end Layer
end YM.RegulatorIR.Budget
