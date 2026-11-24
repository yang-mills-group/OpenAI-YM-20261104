import YM.MSbar.Image.Train
/-! Evaluation in log κ. Use only momentum loops (finite coefficient stances).
 Don't forget exp reweighting BEFORE dropping ε & hat sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Image
open Dim Symbol Domain Diagram Function Set Filter Play Play.Deck Category Counter Super Scale Counter.Crest Complex Metric Finset
open scoped Classical Topology BigOperators
variable {C:Type}{U V:Set ℂ}{W:Edition C}{d c e:Bit}{X Y:Film C}{t k n:ℕ} {z:ℂ} (a:ℂ)
def bill (U:Set ℂ)(W:Edition C)(d:Bit)(t:ℕ)(X:Film C)(a:ℂ)(i:ℕ): Vertex C:= reader U W d (follow a i t X)
def pole (a z:ℂ):ℂ:=cexp (a*2*z)
namespace Bill
variable [Profit U] [Profit V] (h:Ready U W d n X)(g:Ready U W d n Y)
include h
lemma live : Live W d (bill U W d n X a k):= Reader.live (flight a h)
lemma region (he: V⊆U): bill V W d n X a k=bill U W d n X a k:=Reader.region (flight a h) he
-- remove extraneous h in scope
omit h in
lemma empty : bill U W d n 0 a t=0:= by rw [bill,show follow a t n (0:Film C)=0 from (by ext; simp [follow,times]),Reader.empty]
lemma expand (c:ℂ): bill U W d n (c • X) a k=c • bill U W d n X a k:=by rw [bill,bill,← Reader.times (flight a h),show follow a k n (c • X)=c • follow a k n X from ?_]; funext z; simp only [follow,Finset.sum_apply,times,Pi.smul_apply, Finset.smul_sum]; apply sum_congr rfl; intros; apply smul_comm
-- Θ since χ0 read only no counter
lemma watch (hx:z∈rim U): follow a 0 n X z=(leaf n (pole a z) (shutter W d X z)).val:=by
    rw [leaf_eq,Submodule.coe_sum]; simp only [follow,Finset.sum_apply,times]; apply Finset.sum_congr rfl; intro i hi
    rw [Submodule.coe_smul_of_tower,shutter,plug_eq (h.lives hx i), pole, ← Complex.exp_nat_mul]; simp only [rides,Scale.slope,step,pow_zero,mul_one]
    ring_nf -- inside exp
lemma line (H:∀ k', EqOn (Y k') (X k') (rim U)): bill U W d n Y a k=bill U W d n X a k:= Reader.equal (flight a h) (fun z hz=> by simp only [follow,Finset.sum_apply,times,H _ hz])
include g
lemma add : bill U W d n (X+Y) a k=bill U W d n X a k+bill U W d n Y a k := by rw [bill,bill,bill,← Reader.plus (flight a h) (flight a g), show follow a k n (X+Y)= _ from (show follow a k n (X+Y)= follow a k n X+follow a k n Y from (by ext1 z; simp [follow,times,Finset.sum_add_distrib]))]
lemma sub : bill U W d n (X-Y) a k=bill U W d n X a k-bill U W d n Y a k:= by rw [sub_eq_add_neg,sub_eq_add_neg,← neg_one_smul ℂ Y, add a h (g.scale _),expand a g]; simp
omit g
omit h in
lemma total {α:Type*}(I:Finset α){A:α→Film C}(h:∀ i∈I,Ready U W d n (A i)): bill U W d n (∑ i∈I,A i) a k=∑ i∈I,bill U W d n (A i) a k:=by induction I using Finset.induction_on with| empty=>simp [Bill.empty] | insert i s he ih=> rw [sum_insert he,sum_insert he, add a (h _ (mem_insert_self ..)) (Ready.sum s (fun j hj=> h _ (mem_insert_of_mem hj))),ih (fun j hj=>h _ (mem_insert_of_mem hj))]
local notation "V^" => bill U W d n X a 0
lemma post {A:Mono W d e} (hA:Linear A): bill U W e n (Play.spin A X) a 0=(A 0 (plug W d V^)).val:=by
    rw [bill,bill,← Reader.post (flight (i:=0) a h) hA]; refine Reader.equal (bound_linear hA (flight a h)) fun z hz=> ?_; rw [watch a (h.spins hA) hz, shutter_spin,leaf_act,Play.post,watch a h hz,plug_val]
lemma delay {A:Mono W d e}(hA:Linear A): bill U W e (n+1) (Play.delay A X) a 0=(A 0 (plug W d V^)).val:= by
    let Y:=follow a 0 (n+1) (Play.delay A X); let L:=Play.post A (follow a 0 n X); have hp:=bound_linear hA (flight (i:=0) a h); have ht:DifferentiableOn ℂ (pole a) U:= by unfold pole; fun_prop
    have H: EqOn Y (times (pole a) L) (rim U):=by intro z hz; dsimp only [Y,L,times]; rw [watch a (h.later hA) hz, shutter_delay,leaf_sea,Play.post,watch a h hz,plug_val]; rfl
    rw [bill,Reader.equal (hp.unit ht) H,Reader.holm hp ht]; simp only [pole,mul_zero,Complex.exp_zero,one_smul]; exact Reader.post (flight a h) hA
lemma twin {A:Poly W d c e}(g:Ready U W c t Y) (hA:Polarized A): bill U W e (n+t) (make A X Y) a 0=(A 0 (plug W d V^) (plug W c (bill U W c t Y a 0))).val :=by
    refine Eq.trans (Reader.equal (bound_poly hA (flight a h) (flight a g)) ?_) (Reader.twin (flight a h) (flight a g) hA); intro z hz; rw [watch a (h.bottled g hA) hz, shutter_make, leaf_knots _ le_rfl (Need h.cutoff) (Need g.cutoff), ← leaflet (Need h.cutoff) (Nat.le_add_right ..),← leaflet (Need g.cutoff) (Nat.le_add_left ..), Play.twin, watch a h hz, watch a g hz, plug_val,plug_val]
end Bill
end YM.MSbar.Image
