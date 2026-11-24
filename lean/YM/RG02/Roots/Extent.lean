import YM.RG02.Roots.Radius

/-!
# Span of a connected kernel diagram

Keep physical positions for field legs, distinguished marks, placement roots,
path/test anchor offsets etc. Use ANY projection syntax with all incidence
relations shown, fixed number of indices. Potential polarization may
increase that number. For obtaining tensor norm of course *every free
position in a sum is an index*. In particular tag overlaps charge singleton
costs even at a vertex with no contracted legs. Many-to-one anchors allowed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Roots
open Function Finset MeasureTheory Lattice Wilson Marker Extra.Trajectories Marks Wick Wick.Actor
open scoped BigOperators Classical
variable {I V A B : Type}[DecidableEq I][Fintype I]{D : I→Type}{n : Side}
variable [DecidableEq V] {R : Census V}[DecidableEq A][Fintype A][DecidableEq B]

lemma extension (Y : Finset V)(u : V→ Site n)(d : V→V→Prop)(h : NoCut Y d){w : ℕ}
    (hf : ∀ i∈Y,∀ j∈Y,d i j→ separation (u i) (u j)≤w){x y : V}(hx : x∈Y)(hy:y∈Y):
    separation (u x) (u y)≤Y.card*w := by
   suffices he : ∀ X:Finset V,X⊆Y→x∈X → (∀ i∈X,separation (u x) (u i)≤ X.card*w) → separation (u x) (u y)≤ Y.card*w from he {x} (singleton_subset_iff.mpr hx) (mem_singleton_self _) (fun i hi=>by rw [mem_singleton.mp hi,separation_self]; omega)
   have hr k : ∀ X:Finset V,X⊆Y→(Y\X).card=k →x∈X → (∀ i∈X,separation (u x) (u i)≤ X.card*w) → separation (u x) (u y)≤ Y.card*w:=by
      induction k with
      | zero => intro X hX hx hb he; rw [show Y=X from Finset.Subset.antisymm (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hx)) hX] at hy ⊢; exact he _ hy
      | succ k ih=>
        intro X hl hX hK he
        obtain ⟨j,hj,v,hv,hg⟩:= h X hl ⟨x,hK⟩ (card_pos.mp (by rw [hX]; omega))
        obtain ⟨ha,hh⟩:= mem_sdiff.mp hv
        refine ih (insert v X) (insert_subset ha hl) ?_ (mem_insert_of_mem hK) ?_
        · rw [card_sdiff_of_subset (insert_subset ha hl),card_insert_of_notMem hh]; rw [card_sdiff_of_subset hl] at hX; omega
        intro t ht
        rw [card_insert_of_notMem hh,add_mul,one_mul]
        rcases mem_insert.mp ht with ht|ht
        · subst t; exact (separation_triangle (u x) (u j) (u v)).trans (Nat.add_le_add (he j hj) (hf _ (hl hj) _ ha hg))
        exact (he t ht).trans (Nat.le_add_right ..)
   exact fun X hX => hr _ X hX rfl

abbrev Records (A : Type) [DecidableEq A][Fintype A] := Multi.Hot (full A)
abbrev Factors (A V : Type)[DecidableEq A][Fintype A] := V ⊕ Records A

structure Bones (V A B : Type)[DecidableEq A][Fintype A] where
  base : Factors A V → B
  touches : Factors A V → Finset B
  appoint (i : Factors A V) : base i ∈ touches i

def load (q : Bones V A B)(t : B→Site n)(f : Factors A V) :=
   ∑ b ∈ q.touches f,separation (t (q.base f)) (t b)
structure Names (q:Bones V A B)(o : A→V)(x:R.Mode)(p:(Lines A).Mode) : Prop where
   connects (u:Records A) (hu : u∈p.val)(i:V) (hi:i∈paidFor o u) : ¬ Disjoint (q.touches (.inl i)) (q.touches (.inr u))
   whole (b:B) : ∃ i∈ (Pair.mk x p).val,b∈q.touches i

variable (o : A→ V){x:R.Mode}{p:(Lines A).Mode}(Y : Bones V A B)(T : Factors A V → ℕ)(t : B→Site n)

/-- Complete exposure used in proof. Not gas weight. -/
def width (x : R.Mode)(p:(Lines A).Mode) := ∑ i∈(Pair.mk x p).val,(Roots.load Y t i+T i)

-- use explicit arguments (not dot precedence)
local notation "W" => width Y T t x p

omit [DecidableEq B] in
lemma reach {b : B}{i : Factors A V} (hi : i∈(Pair.mk x p).val) (hv : b∈Y.touches i):
    separation (t (Y.base i)) (t b)≤ W :=by
   
   refine le_trans (b:=Roots.load Y t i+T i) (le_trans ?_ (Nat.le_add_right ..)) (Finset.single_le_sum (fun a (_:a∈(Pair.mk x p).val)=> Nat.zero_le (Roots.load Y t a+T a)) hi)
   exact (Finset.single_le_sum (fun j (_:j∈Y.touches i)=> Nat.zero_le (separation (t (Y.base i)) (t j))) hv)

omit [DecidableEq B] in
lemma base_dist {z r : Factors A V}(hz : z∈ (Pair.mk x p).val)(hr : r∈(Pair.mk x p).val)(H : ¬ Disjoint (Y.touches z) (Y.touches r)) :
    separation (t (Y.base z)) (t (Y.base r)) ≤ 2*W :=by
   obtain ⟨b,hb,h⟩:=Finset.not_disjoint_iff.mp H
   have he:= reach Y T t hr h
   rw [two_mul]; apply (separation_triangle (t (Y.base z)) (t b) _).trans; rw [separation_comm (t b)]
   exact Nat.add_le_add (reach Y T t hz hb) he

variable (H : Names Y o x p)(hk : Paired o (Pair.mk x p))(F:I → Site n)
def account (Y : Bones V A B)(T : Factors A V → ℕ)(t : B→Site n)(F : I → Site n)(i : Factors A V) := dots F (t (Y.base i)) (T i)

include H
omit [DecidableEq B] in
lemma tag_link {i : V}(hi : i∈x.val){u : I}(hh:u∈ budget (fun j=> account Y T t F (.inl j)) (fun j => account Y T t F (.inr j)) o p i) :
    separation (t (Y.base (.inl i))) (F u) ≤ 3*W :=by
   let z:= Pair.mk x p
   have hp (j) (hj:j∈z.val) : T j ≤ W := (Nat.le_add_left _ (Roots.load Y t j)).trans (Finset.single_le_sum (fun k (_:k∈z.val)=>Nat.zero_le (Roots.load Y t k+T k)) hj)
   have ha : Sum.inl i∈ (Pair.mk x p).val := inl_mem_disjSum.mpr hi
   rcases mem_union.mp hh with hh|hh
   · have he:= (mem_filter.mp hh).2
     exact (he.trans (hp _ ha)).trans (by omega)
   obtain ⟨j,hj,hu⟩:= mem_biUnion.mp hh; obtain ⟨hK,hC⟩ := mem_filter.mp hj
   have he := H.connects j hK i hC
   have hv:= (mem_filter.mp hu).2
   have hZ : Sum.inr j∈z.val:= inr_mem_disjSum.mpr hK
   refine (separation_triangle (t (Y.base (.inl i))) (t (Y.base (.inr j))) (F u)).trans ((Nat.add_le_add (base_dist Y T t ha hZ he) (le_trans hv (hp _ hZ))).trans ?_)
   omega

include hk
variable (h : NoCut x.val (graph (fun j=>account Y T t F (.inl j)) (fun j=>account Y T t F (.inr j)) o p))
include h

def rateLoss (x:R.Mode) := 16*(x.val.card+1)
omit [DecidableEq B] in
lemma global {i : V}(hi : i∈x.val)(b : B) : separation (t (Y.base (.inl i))) (t b) ≤ rateLoss x * W := by
   have hX : CompleteOn (arms o x.val) p:= by simpa only [Paired,Pair.fst_mk,Pair.snd_mk] using hk
   have hu {j : V}(hj:j∈x.val) : separation (t (Y.base (.inl i))) (t (Y.base (.inl j))) ≤ x.val.card * (6*W) := by
      refine extension x.val (fun i=>t (Y.base (.inl i))) _ h ?_ hi hj
      intro u hu v hv HH
      rcases HH with ⟨p',h₁,h₂,h₃⟩|H'
      · refine (separation_triangle (t (Y.base (.inl u))) (t (Y.base (.inr p'))) (t (Y.base (.inl v)))).trans ?_
        rw [separation_comm _ (t (Y.base (.inl v)))]
        have ha : Sum.inr p'∈(Pair.mk x p).val := inr_mem_disjSum.mpr h₁
        refine (Nat.add_le_add (base_dist Y T t (show Sum.inl u∈ (Pair.mk x p).val from inl_mem_disjSum.mpr hu) ha ?_) (base_dist Y T t (show Sum.inl v∈(Pair.mk x p).val from inl_mem_disjSum.mpr hv) ha ?_)).trans (by omega)
        · exact H.connects p' h₁ _ h₂
        exact H.connects p' h₁ _ h₃
      obtain ⟨s,ha,hb⟩ := not_disjoint_iff.mp H'
      refine (separation_triangle (t (Y.base (.inl u))) (F s) (t (Y.base (.inl v)))).trans ?_
      rw [separation_comm _ (t (Y.base (.inl v)))]; refine (Nat.add_le_add (tag_link o Y T t H F hu ha) (tag_link o Y T t H F hv hb)).trans (by omega)
   obtain ⟨a,ha,hb⟩:= H.whole b
   rcases a with a|a
   · have hl:= Nat.add_le_add (hu (j:=a) (inl_mem_disjSum.mp ha)) (reach Y T t ha hb)
     refine (separation_triangle (t (Y.base (.inl i))) (t (Y.base (.inl a))) (t b)).trans (hl.trans ?_)
     unfold rateLoss; nlinarith only [Nat.zero_le W, Nat.zero_le (W*x.val.card)]
   have he:= (inr_mem_disjSum.mp ha)
   obtain ⟨z,hz⟩:= a.property
   have hp: z∈ Multi.Hot.sites a:=hz
   have hP : o z ∈ x.val:= arm_of.mp (hX.1 ▸ mem_biUnion.mpr ⟨a,he,hp⟩)
   have hv : separation (t (Y.base (.inl (o z)))) (t b)≤ 2*W+W:=
      (separation_triangle _ (t (Y.base (.inr a))) _).trans (Nat.add_le_add (base_dist Y T t (show Sum.inl (o z)∈(Pair.mk x p).val from inl_mem_disjSum.mpr hP) ha (H.connects a he (o z) (mem_image_of_mem _ hz))) (reach _ _ _ ha hb))
   refine (separation_triangle (t (Y.base (.inl i))) (t (Y.base (.inl (o z)))) _).trans ((Nat.add_le_add (hu hP) hv).trans ?_)
   unfold rateLoss; nlinarith only [Nat.zero_le W,Nat.zero_le (W*x.val.card)]

section all
variable [Fintype B]
def Tollk (_b : B)(x:R.Mode):= 2*rateLoss x*Fintype.card B

def MetricSize (x:B→Site n)(b:B) := ∑ i:B,separation (x b) (x i)

omit [DecidableEq B] in
lemma paid_span (he : x.val.Nonempty)(b:B) : MetricSize t b ≤ Tollk b x * W :=by
    obtain ⟨i,hi⟩:= he
    have ha b:= global o Y T t H hk F h hi b
    unfold MetricSize
    calc
       _ ≤ ∑ _:B, 2* (rateLoss x*W):= by
          apply sum_le_sum; intro j _; refine (separation_triangle (t b) (t (Y.base (.inl i))) _).trans ?_
          rw [two_mul,separation_comm]; exact Nat.add_le_add (ha _) (ha _)
       _ = _ := by unfold Tollk; rw [sum_const,card_univ, smul_eq_mul]; ring
end all
end YM.RG02.Roots
