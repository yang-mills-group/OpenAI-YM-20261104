import YM.MSbar.Origin.Sprig

/-!
# Bose files evaluated on fermion super alphabet

At common origin. Analytic operations lift compatible germs to super
series. Replaying on maps with real entries (including site evaluations) is
power substitution in the term. No assumptions of locality/alphabet rank bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin
open Function Filter Topology Super
open scoped BigOperators ContDiff InnerProductSpace
variable {α β E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (u : α → E)
def bose (f : E→ℝ) : Term α := Complex.ofReal ∘ sprig u 0 f
@[simp] lemma bose_nil (f : E→ℝ) : bose u f []=(f 0:ℂ) := rfl
lemma bose_step (f : E→ℝ) (a) : peel a (bose u f)=bose u (stunt f (u a)) := rfl
lemma bose_at (f : E→ℝ) (a L) : bose u f (a::L)=bose u (stunt f (u a)) L := rfl
variable {f g : E → ℝ} {p : α→Bool}
lemma bose_congr (h : f=ᶠ[𝓝 0] g) : bose u f=bose u g := by unfold bose; rw [sprig_congr u h]
@[simp] lemma bose_zero : bose u 0=0 := by ext L; simp [bose,sprig_zero]
lemma bose_add (F : Eager f 0) (G : Eager g 0) : bose u (f+g)=bose u f+bose u g := by ext L; simp only [bose,sprig_add u F G,comp_apply, Complex.ofReal_add,Pi.add_apply,Complex.ofReal_add]
lemma bose_neg (F : Eager f 0) : bose u (-f)= -bose u f := by ext L; simp only [bose,sprig_neg u F,comp_apply,Pi.neg_apply,Complex.ofReal_neg]
lemma bose_sub (F : Eager f 0) (G : Eager g 0) : bose u (f-g)=bose u f-bose u g := by rw [sub_eq_add_neg, bose_add u (g:=-g) F G.neg,bose_neg u G,sub_eq_add_neg]
lemma bose_smul (F : Eager f 0) (c : ℝ) : bose u (c • f)=(c:ℂ) • bose u f := by ext L; simp [bose,sprig_smul u c F]
lemma bose_sum {s : Finset β} {f : β → E → ℝ} (h : ∀ i∈s,Eager (f i) 0) : bose u (∑ i∈s,f i)=∑ i∈s,bose u (f i) := by ext L; simp only [bose,sprig_sum u s f h, comp_apply,Finset.sum_apply, Complex.ofReal_sum]
lemma bose_comp [NormedAddCommGroup H] [NormedSpace ℝ H] {f : H → ℝ} (V : E→L[ℝ] H) (h : Eager f 0) : bose u (f ∘ V)=bose (V ∘ u) f := by unfold bose; rw [sprig_comp u V]; rw [map_zero]; rwa [map_zero]
lemma bose_peel_vanish {a : α} (h : u a=0) (f : E→ℝ) : peel a (bose u f)=0 := by ext L; simp [bose,sprig_dies u f h]
lemma bose_order (f : E→ℝ) (F : Eager f 0) (W : ∀ a,p a=true → u a=0) : Ordered p (bose u f) := by
  intro A a b L; induction A generalizing f with
  | nil =>
    have he : bose u f (a::b::L)=bose u f (b::a::L) := congrArg Complex.ofReal (sprig_agree u F a b L)
    cases ha : p a
    · simp [he]
    cases hb : p b
    · simp [he]
    rw [List.nil_append,List.nil_append, he, ← peel_apply b (bose u f), bose_peel_vanish u (W b hb), Pi.zero_apply,mul_zero] -- patch
  | cons k A ih => exact ih (stunt f (u k)) (stunt_eager F _)
lemma bose_grade (f : E→ℝ) (W : ∀ a,p a=true→u a=0) : Grade p false (bose u f) := by
  intro L e; induction L generalizing f with
  | nil => simp at e
  | cons a L ih => cases ha : p a <;> simp [ha] at e
                   · exact ih (stunt f _)  (by simp [e])
                   rw [←peel_apply a (bose u f),bose_peel_vanish u (W a ha) f]; rfl
lemma bose_prod (F : Eager f 0) (G : Eager g 0) (W : ∀ a,p a=true→u a=0) : bose u (f*g)=mix p (bose u f) (bose u g) := by
  funext L; induction L generalizing f g with
  | nil => exact Complex.ofReal_mul ..
  | cons a L ih =>
    have h : stunt (f*g) (u a)=ᶠ[𝓝 0] stunt f (u a)*g+f*stunt g (u a) := by
      filter_upwards [F.eventually (by simp), G.eventually (by simp)] with i x y; simp only [stunt, fderiv_mul (x.differentiableAt (by simp)) (y.differentiableAt (by simp)),Pi.mul_apply,Pi.add_apply,_root_.add_apply, _root_.smul_apply, smul_eq_mul]; ring
    have he := stunt_eager F (u a); have hp := stunt_eager G (u a)
    rw [← peel_apply a (mix _ _ _), (bose_grade u f W).peel_mix,Pi.add_apply,bose_at,bose_congr u h,bose_add (f:=stunt f (u a)*g) (g:=f*stunt g (u a)) u (he.mul G) (F.mul hp)];
    simp only [bose_step,twist_false',one_smul,Pi.add_apply, ih he G, ih F hp]
lemma bose_const (c : ℝ) : bose u (fun _ => c)=scalar (c:ℂ) := by
  funext L; cases L; · rfl
  rename_i a t; rw [bose_at, show stunt (fun _ => c) (u a)=0 from funext fun x => by simp [stunt],bose_zero]; rfl
lemma bose_linear (T : E→L[ℝ] ℝ) (a) (L) : bose u T (a::L)=scalar (T (u a):ℂ) L := by rw [bose_at, show stunt T (u a)=(fun _ => T (u a)) from funext fun _ => by rw [stunt,T.fderiv],bose_const]

section
variable [Fintype α]
lemma stuntRoll (v : β→E) (s : α→β→ℝ) (e : ∀ b,v b=∑ a,s a b • u a) (f : E→ℝ) (b) :
    stunt f (v b)=∑ a,s a b • stunt f (u a) := by funext x; simp [stunt,e] -- lint
lemma replay_bose (v : β→ E) (F : Eager f 0) (s : α→ β→ ℝ) (e : ∀ b,v b=∑ a,s a b • u a) : replay (fun a b => (s a b:ℂ)) (bose u f)=bose v f := by
  funext L; induction L generalizing f with
  | nil => rfl
  | cons b L ih => simp_rw [replay_cons,bose_step, ih (stunt_eager F _), bose_at, stuntRoll u v s e f b, bose_sum v (f:=fun a : α => s a b • stunt f (u a)) (fun a _ => (stunt_eager F (u a)).const_smul (s a b)), bose_smul v (stunt_eager F _)]; simp
omit [Fintype α] in
lemma slot_real [DecidableEq β] (φ : α→β) : placeIn φ=(fun a b => (↑(if b=φ a then (1:ℝ) else 0):ℂ)) := by funext a b; by_cases e : b=φ a <;> simp [placeIn,e]
lemma play_bose [DecidableEq β] (v : β→E) (F : Eager f 0) (φ : α→β) (e : ∀ b,v b=∑ a, if b=φ a then u a else 0) : replay (placeIn φ) (bose u f)=bose v f := by rw [slot_real]; exact replay_bose u v F _ (fun b => by simpa [ite_smul] using e b) -- maybe global simp issue
end
end YM.MSBar.Origin
