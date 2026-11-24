import YM.FormalBulk08.Aster.Fig

/-! Arbitrary changing alphabets (depending on scales). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Function Filter Lava Gorge
open scoped Topology ENNReal BigOperators Classical
variable {X Z I : Type*} (t:Time X) {V : X→ Type*}{m n:ℕ} (R : ∀ x, Reach (V x)) (σ δ : X→ℝ) {T U: (x:X)→ Tile (V x) m}

def Cost (T:(x:X)→ Tile (V x) m): Prop := ∃ C:X→ℝ, Soft t C ∧ ∀ x, Bail (R x) (σ x) (T x) (C x)
def Dust (T:(x:X)→ Tile (V x) m): Prop := ∃ C:X→ℝ, Soft t C ∧ (∀ x,0≤C x) ∧ ∀ x, Bail (R x) (σ x) (T x) (C x*δ x)
structure Totem (T U: (x:X)→ Tile (V x) m): Prop where
   left: Cost t R σ T
   right: Cost t R σ U
   nebula : Dust t R σ δ (fun i=> T i-U i)
lemma cost_void (m:ℕ):Cost t R σ (fun i=> (0:Tile (V i) m)):= ⟨_,soft_coin t 0,fun _=>bail_void ..⟩
lemma dust_void (m): Dust t R σ δ (fun i=> (0:Tile (V i) m)):= ⟨_,soft_coin t 0,fun _=>le_rfl,fun i=>by rw [zero_mul];apply bail_void⟩
lemma voids (m):Totem t R σ δ (fun i=>(0:Tile (V i) m)) (fun _=> 0) := ⟨cost_void ..,cost_void ..,by simp_rw [sub_self];apply dust_void⟩
variable {t R σ δ}
lemma Cost.links (h:Cost t R σ T)(f:Z→ X): Cost (t.reach f) (fun z=> R (f z)) (σ∘f) (fun z=> T (f z)):= by obtain ⟨B,b,H⟩:=h; exact ⟨_,b.reach f,fun _=> H _⟩
lemma Dust.links (h:Dust t R σ δ T)(f:Z→ X): Dust (t.reach f) (fun z=> R (f z)) (σ ∘f) (δ∘f) (fun z=> T (f z)):=by obtain ⟨B,b,H,h⟩:=h; exact ⟨_,b.reach f,fun _=>H _,fun _=> h _⟩
lemma Dust.wanes {D:X→ℝ}(h:Dust t R σ δ T)(e:∀ i, δ i ≤ D i): Dust t R σ D T:= by obtain ⟨B,b,H,h⟩:= h; exact ⟨_,b,H,fun i=>(h i).mono (mul_le_mul_of_nonneg_left (e i) (H i))⟩
lemma Totem.links (h:Totem t R σ δ T U)(f:Z→X): Totem (t.reach f) (fun z=> R (f z)) (σ∘f) (δ∘f) (fun z=> T (f z)) (fun z=> U (f z)):= ⟨h.left.links f,h.right.links f,h.nebula.links f⟩
lemma Totem.wanes {D:X→ℝ}(h:Totem t R σ δ T U)(e:∀ i, δ i ≤ D i): Totem t R σ D T U:= ⟨h.left,h.right,h.nebula.wanes e⟩
lemma Cost.plus (h:Cost t R σ T)(e:Cost t R σ U): Cost t R σ (fun i=> T i+ U i):= by obtain ⟨B,b,H⟩:= h; obtain ⟨C,c,E⟩:= e; exact ⟨_,b.plus c,fun i=>(H i).add (E i)⟩
lemma Cost.minus (h:Cost t R σ T)(e:Cost t R σ U): Cost t R σ (fun i=> T i-U i):= by obtain ⟨B,b,H⟩:=h; obtain ⟨C,c,E⟩:=e; exact ⟨_,b.plus c,fun i=> (H i).sub (E i)⟩
lemma Cost.reverse (h:Cost t R σ T) : Cost t R σ (fun i=> -T i) := by obtain ⟨B,b,H⟩:= h; exact ⟨_,b,fun i=>(H i).neg⟩
lemma Dust.plus (h:Dust t R σ δ T)(e:Dust t R σ δ U): Dust t R σ δ (fun i=> T i + U i):= by obtain ⟨B,b,b',H⟩:= h; obtain ⟨C,c,c',E⟩:= e; exact ⟨_,b.plus c,fun i=>add_nonneg (b' i) (c' i),fun i=>by rw [add_mul]; exact (H i).add (E i)⟩
lemma Dust.reverse (h:Dust t R σ δ T): Dust t R σ δ (fun i=> -T i):= by obtain ⟨B,b,b',H⟩:= h; exact ⟨_,b,b',fun i=>(H i).neg⟩
variable {f g:X→ℝ}
lemma Cost.amp (h:Cost t R σ T)(e:Soft t f): Cost t R σ (fun i=> f i • T i):=by obtain ⟨B,b,H⟩:= h; exact ⟨_, e.radius.times b,fun i=>(H i).smul _⟩
lemma Cost.damp (h:Cost t R σ T)(e:Faint t δ f): Dust t R σ δ (fun i=> f i • T i):= by
    obtain ⟨A,b,H⟩:=h; obtain ⟨C,c,c',E⟩:=e; refine ⟨_, c.times b,fun i=> mul_nonneg (c' i) (H i).1,fun i=>?_⟩; rw [mul_right_comm]; exact ((H i).smul _).mono (mul_le_mul_of_nonneg_right (E i) (H i).1)
lemma Dust.amp (h:Dust t R σ δ T)(e:Soft t f): Dust t R σ δ (fun i=>f i • T i):=by obtain ⟨A,b,b',H⟩:=h; refine ⟨_,e.radius.times b,fun i=> mul_nonneg (abs_nonneg _) (b' i),fun i=>?_⟩; rw [mul_assoc]; exact (H i).smul _
lemma Cost.polish (h:Cost t R σ T) : Cost t R σ (fun i=>sand (T i)) := by obtain ⟨A,a,H⟩:=h; exact ⟨_,a,fun i=>(H i).smooth⟩
lemma Totem.polish (h:Totem t R σ δ T U): Totem t R σ δ (fun i=>sand (T i)) (fun i=> sand (U i)):= by
    obtain ⟨A,b,b',H⟩:=h.nebula; refine ⟨h.left.polish,h.right.polish,A,b,b',fun i=>?_⟩; convert (H i).smooth using 1; ext;simp only [sand, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
lemma Cost.lengthen (h:Cost t R σ T)(e:m=n): Cost t R σ (fun i=>lengthen e (T i)):= by subst m; exact h
lemma Totem.lengthen (h:Totem t R σ δ T U)(e:m=n): Totem t R σ δ (fun i=> lengthen e (T i)) (fun i=> lengthen e (U i)):=by subst m; exact h
variable {T' U': (x:X)→ Tile (V x) m}
lemma Totem.constant (h:Cost t R σ T): Totem t R σ δ T T:= ⟨h,h,by simp_rw [sub_self];apply dust_void⟩
lemma Totem.plus (h:Totem t R σ δ T U)(e:Totem t R σ δ T' U'): Totem t R σ δ (fun i=> T i+ T' i) (fun i=> U i+ U' i):= by
    refine ⟨h.left.plus e.left,h.right.plus e.right,?_⟩; convert h.nebula.plus e.nebula using 1;ext1;abel
lemma Totem.reverse (h: Totem t R σ δ T U): Totem t R σ δ (fun i=> -T i) (fun i=> -U i):= by
   refine ⟨h.left.reverse,h.right.reverse,?_⟩; convert h.nebula.reverse using 1; ext1;abel
lemma Totem.minus (h:Totem t R σ δ T U)(e:Totem t R σ δ T' U'): Totem t R σ δ (fun i=> T i- T' i) (fun i=> U i-U' i):=by simp_rw [sub_eq_add_neg];exact h.plus e.reverse
lemma Totem.amp (h:Totem t R σ δ T U)(e:Pact t δ f g): Totem t R σ δ (fun i=> f i • T i) (fun i=> g i • U i):= by
    refine ⟨h.left.amp e.left,h.right.amp e.right,?_⟩; convert (h.nebula.amp e.left).plus (h.right.damp e.blur) using 1; ext i x; simp;ring
lemma totem_sums (P:Finset I){T U:I→ (x:X)→ Tile (V x) m}(h:∀ i∈P,Totem t R σ δ (T i) (U i)):
    Totem t R σ δ (fun x=>∑ i∈P,T i x) (fun x=>∑ i∈P,U i x):= by
   induction P using Finset.induction with
   | empty=> simp only [Finset.sum_empty];apply voids
   | @insert i P he ih=>simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma cost_sums (P:Finset I){T:I→ (x:X)→ Tile (V x) m}(h:∀ i∈P,Cost t R σ (T i)): Cost t R σ (fun x=>∑ i∈P,T i x):=(totem_sums P (fun i hi=>Totem.constant (δ:=fun _=>0) (h i hi))).left
lemma cost_pay (P:Finset I){m:I→ℕ}{T:(i:I)→ (x:X)→Tile (V x) (m i)}(hp:∀ i∈P,Cost t R σ (T i)):∃ B:X→ℝ,Soft t B ∧ (∀ i, 0≤B i) ∧ ∀ i∈P,∀ x, Bail (R x) (σ x) (T i x) (B x) := by
    induction P using Finset.induction with
    | empty=>exact ⟨_,soft_coin _ 0,by simp,by simp⟩
    | @insert i P he ih=> obtain ⟨B,b,H,Q⟩:= ih fun i hi=> hp i (Finset.mem_insert_of_mem hi); obtain ⟨A,a,U⟩:= hp i (Finset.mem_insert_self ..); refine ⟨_, b.plus a,fun x=>add_nonneg (H x) (U x).1,fun j hj x=>?_⟩; rcases Finset.mem_insert.mp hj with rfl|hj;exact (U x).mono (le_add_of_nonneg_left (H x)); exact (Q j hj x).mono (le_add_of_nonneg_right (U x).1)
lemma dust_pay (P:Finset I){m:I→ℕ}{T:(i:I)→ (x:X)→Tile (V x) (m i)}(e:∀ i,0≤δ i)(hp:∀ i∈P,Dust t R σ δ (T i)):
     ∃ B:X→ℝ,Soft t B ∧ (∀ i,0≤B i) ∧ ∀ i∈P,∀ x, Bail (R x) (σ x) (T i x) (B x*δ x):= by
    induction P using Finset.induction with
    | empty=> exact ⟨_,soft_coin t 0,by simp,by simp⟩
    | @insert i P he ih=> obtain ⟨A,a,H,Q⟩:= ih fun j hj=>hp j (Finset.mem_insert_of_mem hj);obtain ⟨B,b,h,U⟩:=hp i (Finset.mem_insert_self ..); refine ⟨_,a.plus b,fun x=>add_nonneg (H x) (h x), fun j hj x=>?_⟩; rw [add_mul]; rcases Finset.mem_insert.mp hj with rfl|hj;exact (U x).mono (le_add_of_nonneg_left (mul_nonneg (H x) (e x))); exact (Q j hj x).mono (le_add_of_nonneg_right (U x).1)
end YM.FormalBulk08.Aster
