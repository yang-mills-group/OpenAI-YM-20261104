import YM.FormalBulk08.Glide.Post

/-!
# Powers of arbitrary admissible local age functions. `τ` may itself
vary with announcements; THIS power never depends on block or cutoff or moving
schedule index in a proved theorem for a funded family.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Function Filter Lava Gorge
open scoped Topology ENNReal BigOperators Classical
variable {X Z I : Type*}

structure Time (X:Type*) where
   day : X→ℝ
   one : ∀ x, 1≤day x
variable (t:Time X)
lemma Time.good (x:X): 0≤ t.day x:= zero_le_one.trans (t.one x)
def Time.reach (g:Z→X): Time Z:=⟨fun z=> t.day (g z),fun z=> t.one (g z)⟩

def Soft (f:X→ℝ): Prop := ∃ C:ℝ, ∃ n:ℕ, 0≤C ∧ ∀ x,|f x| ≤ C*(t.day x)^n
lemma soft_coin (c:ℝ): Soft t (fun _=>c) := ⟨|c|,0,abs_nonneg _,by simp⟩
lemma soft_day : Soft t t.day := ⟨1,1,zero_le_one,fun i=>by rw [abs_of_nonneg (t.good _),pow_one,one_mul]⟩
variable {t} {f g δ : X→ℝ}
lemma Soft.below (h:Soft t f)(he:∀ i, |g i|≤|f i|): Soft t g := by obtain ⟨C,n,h,H⟩:=h; exact ⟨C,n,h,fun i=>(he i).trans (H i)⟩
lemma Soft.radius (h:Soft t f): Soft t (fun i=> |f i|) := h.below (fun i=>by rw [abs_abs])
lemma Soft.plus (h:Soft t f)(e:Soft t g): Soft t (fun i=> f i+ g i) := by
    obtain ⟨C,n,h,H⟩:=h; obtain ⟨D,m,e,E⟩:=e; refine ⟨C+D,max n m,add_nonneg h e,fun i=>?_⟩; rw [add_mul]; exact (abs_add_le ..).trans (add_le_add ((H i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (t.one i) (le_max_left ..)) h)) ((E i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (t.one i) (le_max_right ..)) e)))
lemma Soft.minus (h:Soft t f): Soft t (fun i=>-f i):= h.below (fun i=>by rw [abs_neg])
lemma Soft.times (h:Soft t f)(e:Soft t g): Soft t (fun i=> f i* g i) := by
    obtain ⟨C,n,h,H⟩:=h; obtain ⟨D,m,e,E⟩:=e; refine ⟨C*D,n+m,mul_nonneg h e,fun i=>?_⟩; rw [abs_mul,pow_add]; refine (mul_le_mul (H i) (E i) (abs_nonneg _) ((abs_nonneg _).trans (H i))).trans_eq ?_;ring
lemma Soft.pows (h:Soft t f)(n:ℕ): Soft t (fun i=> f i^n):= by
   induction n with
   | zero=> simpa only [pow_zero] using soft_coin t (1:ℝ)
   | succ n ih=>simp_rw [pow_succ]; exact ih.times h
lemma Soft.reach (h:Soft t f)(g:Z→X): Soft (t.reach g) (fun z=> f (g z)) := by obtain ⟨B,n,h,H⟩:=h; exact ⟨B,n,h,fun i=>H _⟩
lemma soft_bill (U:Finset I){f:I→X→ℝ}(h:∀ i∈U,Soft t (f i)): Soft t (fun x=>∑ i∈U,f i x) := by
    induction U using Finset.induction with
    | empty=>simp only [Finset.sum_empty];apply soft_coin
    | @insert i I he ih=> simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
-- δ may be negative but not used for upgrades
variable (t δ)
def Faint (f:X→ℝ): Prop := ∃ K:X→ℝ, Soft t K ∧ (∀ i,0≤K i) ∧ ∀ i, |f i|≤K i*δ i
lemma faint_zero : Faint t δ 0 := ⟨0,soft_coin _ _,by simp,by simp⟩
structure Pact (f g : X→ℝ): Prop where
   left : Soft t f
   right : Soft t g
   blur : Faint t δ (f-g)
lemma Pact.coin (c:ℝ):Pact t δ (fun _=>c) (fun _=>c) := ⟨soft_coin t c,soft_coin t c,by rw [sub_self];apply faint_zero⟩ -- equality odd
variable {t δ}
lemma Faint.link {h:X→ℝ}(u:Faint t δ h)(f:Z→ X): Faint (t.reach f) (δ∘f) (fun z=>h (f z)):= by
    obtain ⟨K,hK,H,he⟩:=u; exact ⟨K ∘f,hK.reach f,fun z=>H _,fun z=>he _⟩
lemma Faint.lower (h:Faint t δ f) (e:∀ x, |g x|≤|f x|) : Faint t δ g := by obtain ⟨K,u,h,H⟩:= h; exact ⟨K,u,h,fun i=>(e i).trans (H i)⟩
lemma Faint.wane {u:X→ℝ}(h:Faint t δ f)(e:∀ i, δ i≤u i): Faint t u f:= by obtain ⟨K,h,H,hx⟩:= h; exact ⟨K,h,H,fun i=>(hx i).trans (mul_le_mul_of_nonneg_left (e i) (H i))⟩
lemma Faint.plus (h:Faint t δ f)(e:Faint t δ g): Faint t δ (fun x=> f x+g x):= by
    obtain ⟨K,h,H,hx⟩:= h; obtain ⟨L,l,E,el⟩:=e; refine ⟨_,h.plus l, fun i=>add_nonneg (H i) (E i),fun i=>?_⟩; rw [add_mul]; exact (abs_add_le ..).trans (add_le_add (hx i) (el i))
lemma Faint.times (h:Faint t δ f)(hg:Soft t g): Faint t δ (fun x=> f x*g x):= by
    obtain ⟨K,h,H,hx⟩:=h; refine ⟨_,h.times hg.radius, fun i=> mul_nonneg (H i) (abs_nonneg _),fun i=> ?_⟩; rw [abs_mul, mul_right_comm (K i)]; exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
lemma Faint.pact (h:Faint t δ f)(e:∀ i, δ i≤ 1): Soft t f := by
    obtain ⟨K,h,H,hx⟩:=h; exact h.below fun i=> (hx i).trans ((mul_le_of_le_one_right (H i) (e i)).trans (le_abs_self _))
lemma Pact.constant (h:Soft t f) : Pact t δ f f:= ⟨h,h,by rw [sub_self];apply faint_zero⟩
lemma Pact.link (h:Pact t δ f g) (u: Z→X): Pact (t.reach u) (δ∘u) (fun z=> f (u z)) (fun z=> g (u z)):= ⟨h.left.reach u,h.right.reach u,h.blur.link u⟩
variable {f' g':X→ℝ}
lemma Pact.plus (h:Pact t δ f g)(e:Pact t δ f' g'): Pact t δ (fun x=> f x+ f' x) (fun x=> g x+g' x):= ⟨h.left.plus e.left,h.right.plus e.right,(h.blur.plus e.blur).lower (fun i=>le_of_eq (congr_arg _ (by dsimp;ring)))⟩
lemma Pact.neg (h:Pact t δ f g): Pact t δ (fun i=> -f i) (fun i=> -g i):=by
   refine ⟨h.left.minus,h.right.minus,h.blur.lower fun i=>?_⟩; change |-f i - -g i|≤|f i-g i|; rw [neg_sub_neg, abs_sub_comm]
lemma Pact.minus (h:Pact t δ f g)(e:Pact t δ f' g'): Pact t δ (fun x=>f x-f' x) (fun x=>g x-g' x) := by simp_rw [sub_eq_add_neg]; exact h.plus e.neg
lemma Pact.times (h:Pact t δ f g)(e:Pact t δ f' g') : Pact t δ (fun x=> f x* f' x) (fun x=> g x*g' x):=
   ⟨h.left.times e.left,h.right.times e.right,((h.blur.times e.left).plus (e.blur.times h.right)).lower fun i=> le_of_eq (congr_arg _ (by dsimp;ring))⟩
lemma pact_sums (U:Finset I){f g:I→ X→ℝ}(h:∀ i∈U,Pact t δ (f i) (g i)): Pact t δ (fun x=>∑ i∈U,f i x) (fun x=>∑ i∈U,g i x):= by
    induction U using Finset.induction with
    | empty=>simp only [Finset.sum_empty];apply Pact.coin
    | @insert i I he ih=>simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
end YM.FormalBulk08.Aster
