import YM.MSbar.Ward.Panes
/-! Pure-pole correlation of the zero-internal-momentum loop component (key: traces of trees
independent of ζ even when antifields on hats have free indices). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Ken
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{c d e:Bit}{F G:Functionals C}{i k n:ℕ}

abbrev Cold (W:Edition C)(d:Bit)(F:Functionals C):Prop := ∃ k,Winter W d k F
abbrev Sun (W:Edition C)(d:Bit)(F:Functionals C):Prop := ∃ f, Live W d f ∧ F=liftV f
def Peak (W:Edition C)(d:Bit)(n:ℕ)(F:Functionals C):Prop := if n=0 then Sun W d F else Cold W d F
namespace Peak
lemma negc (he:n≠0): Peak W d n F↔ Cold W d F:= by simp [Peak,he]
lemma constant (h:Peak W d 0 F): Sun W d F:= by simpa only [Peak,↓reduceIte] using h
lemma ctr (h:Sun W d F): Peak W d 0 F:= by simpa only [Peak,↓reduceIte] using h
lemma besides (h:Peak W d n F)(z:ℂ): Live W d (F z):= by unfold Peak at h; split_ifs at h; obtain ⟨f,h,rfl⟩:=h; exact h; obtain ⟨_,h⟩:=h; exact h.live z
lemma frozen_sum (h:Cold W d F)(hg:Cold W d G): Cold W d (F+G):=by obtain ⟨m,h⟩:=h; obtain ⟨k,hk⟩:=hg; exact ⟨_,(h.rise (Nat.le_max_left m k)).add (hk.rise (Nat.le_max_right m k))⟩
lemma lift (h:Peak W d n F)(hg:Peak W d n G): Peak W d n (F+G):=by unfold Peak at *; split_ifs at *; obtain ⟨f,hF,rfl⟩:= h; obtain ⟨g,hG,rfl⟩:=hg; exact ⟨f+g, Live.add hF hG,rfl⟩; exact frozen_sum h hg
lemma scale (h:Peak W d n F)(x:ℂ): Peak W d n (x • F):=by unfold Peak at *; split_ifs at *; obtain ⟨f,hF,rfl⟩:= h; exact ⟨_, Live.scale x hF,rfl⟩; obtain ⟨k,h⟩:=h; exact ⟨_,h.scale _⟩
lemma neg (h:Peak W d n F): Peak W d n (-F):= by simpa only [neg_smul,one_smul] using scale h (-1:ℂ)
lemma sub (h:Peak W d n F)(hg:Peak W d n G): Peak W d n (F-G):=by rw [sub_eq_add_neg]; exact h.lift hg.neg
lemma zero (n:ℕ): Peak W d n 0:= by unfold Peak; split_ifs; exact ⟨0,Live.zero,rfl⟩; exact ⟨0,rfl⟩
lemma sum {α:Type*} {A:α→Functionals C}(I: Finset α)(h:∀ i∈I,Peak W d n (A i)): Peak W d n (∑ i∈I,A i):=by induction I using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero _ | insert i s he ih=> rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).lift (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma connection (A:Homo (Deck W d) (Deck W e))(h:Winter W d i F): Winter W e i (Play.post (fun _=>A) F):=by
   induction i generalizing F with
   | zero=> change F=0 at h; rw [h,post_0]; rfl
   | succ i ih=> obtain ⟨f,g,hf,hg,rfl⟩:=h
                 refine ⟨_,_,ih hf,(A (Deck.plug W d g)).property,funext (fun z=>?_)⟩; unfold Play.post winter; dsimp only; rw [Deck.scale' (Live.add hg (hf.live _)), Deck.add' hg (hf.live _),map_smul,map_add]; rfl
lemma cold_post (A:Homo (Deck W d) (Deck W e))(h:Peak W d n F):Peak W e n (Play.post (fun _=>A) F):=by unfold Peak at *; split_ifs at *; obtain ⟨f,h,rfl⟩:=h; exact ⟨_,post_live (F:=liftV f) (fun _=>A) (z:=0),rfl⟩; obtain ⟨i,h⟩:=h; exact ⟨_,connection A h⟩
variable (A:Homo (Deck W d) (Homo (Deck W e) (Deck W c)))
lemma frozen_lhs (h:Cold W d F)(hg: Sun W e G):Cold W c (twin (fun _=> A) F G):=by obtain ⟨k,h⟩:=h; obtain ⟨f,hg,rfl⟩:=hg; exact ⟨_, connection (A.flip (plug W e f)) h⟩
lemma frozen_rhs (h:Sun W d F)(hg: Cold W e G):Cold W c (twin (fun _=>A) F G):= by obtain ⟨f,hg',rfl⟩:=h; obtain ⟨i,h⟩:=hg; exact ⟨_,connection (A (plug W d f)) h⟩
lemma pair_cold (h:Cold W d F)(hg:Cold W e G): Cold W c (twin (fun _=>A) F G):=by
   obtain ⟨i,h⟩:=h; induction i generalizing F with
   | zero => change F=0 at h; rw [h]; simp only [twin_zero]; exact ⟨0,rfl⟩
   | succ i ih=> obtain ⟨f,g,hf,h',rfl⟩:=h; obtain ⟨i',h⟩:= frozen_sum (frozen_rhs (F:=liftV g) A ⟨_,h',rfl⟩ hg) (ih hf)
                 refine ⟨i'+1,_,_,h,Live.zero,funext (fun z=>?_)⟩; unfold twin; rw [winter,winter,Deck.scale' (Live.add h' (hf.live _)),Deck.add' h' (hf.live _),map_smul A, map_add,LinearMap.smul_apply,LinearMap.add_apply,zero_add]; rfl
lemma cross (h:Peak W d i F)(hg:Peak W e k G): Peak W c (i+k) (twin (fun _=>A) F G):=by
   cases i <;> cases k
   · obtain ⟨f,hf,rfl⟩:=constant h; obtain ⟨k,hk,rfl⟩:=constant hg; exact ctr ⟨_,(twin_live (F:=liftV f) (G:=liftV k) (z:=0) (fun _=>A)),rfl⟩
   · exact (negc (by omega)).mpr (frozen_rhs A (constant h) ((negc (by omega)).mp hg))
   · exact (negc (by omega)).mpr (frozen_lhs A ((negc (by omega)).mp h) (constant hg))
   exact (negc (by omega)).mpr (pair_cold A ((negc (by omega)).mp h) ((negc (by omega)).mp hg))
lemma polarized {A:Poly W d e c} (he:∀ z,A z=A 0) (h:Peak W d i F)(hg:Peak W e k G): Peak W c (i+k) (twin A F G):=by rw [funext he]; exact cross _ h hg
end Peak
variable {P:Sites C}{t:ℝ}{l:Bit}{z:ℂ}
lemma tree_plain (hq:Window W l t P)(he:c=l+d+e): tree hq he z=tree hq he 0:= by ext a b:2; exact Subtype.ext (Parallel.sameT a.property b.property z 0)
lemma arrow_plain (h:Pilot univ 0 W c (liftS P))(he : e=c+d):arrow he h z= arrow he h 0 := by ext a:1; exact Subtype.ext (Parallel.sameR a.property z 0)
end YM.MSbar.Play.Ken
