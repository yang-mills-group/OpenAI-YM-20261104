import YM.AllOrder.Ink.Canvas
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
-- arbitrary Λ (order priced; can depend on sign cut by gate anyway)
variable {V : Type} (Λ:V→ℝ)
abbrev face (x:V):=1+|Λ x|
def Grade (U:V→ℝ): Prop:=∃ a:ℝ,∃ k:ℕ, 0≤a ∧ ∀ u, 0≤U u∧U u≤a*(1+|Λ u|)^k
variable {Λ} {U U':V→ℝ}
lemma Grade.nonneg (h:Grade Λ U)(u:V):0 ≤ U u:= by obtain ⟨c,k,h,h'⟩:=h; exact (h' u).1
lemma one_face (x:V):1≤face Λ x:= le_add_of_nonneg_right (abs_nonneg _)
lemma behaves (k:ℕ)(x:V):1≤face Λ x^k:= one_le_pow₀ (one_face _)
lemma gia {Λ: V→ℝ} (b:ℝ)(hb:0≤b):Grade Λ (fun _=>b):= ⟨b,0,hb,fun _=>⟨hb,by simp⟩⟩
lemma givenG (h:∀ x,0≤Λ x):Grade Λ Λ:=⟨1,1,zero_le_one,fun x=>⟨h x,(by simp; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))⟩⟩
lemma Grade.add (h:Grade Λ U)(H:Grade Λ U'): Grade Λ (fun x=> U x+ U' x):= by
 obtain ⟨c,k,h,H'⟩:=h; obtain ⟨d,l,h0,hq⟩:=H; refine ⟨c+d,k+l,add_nonneg h h0,fun i=>⟨add_nonneg (H' i).1 (hq i).1,?_⟩⟩; rw [add_mul]; exact add_le_add ((H' i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_face _) (by omega)) h)) ((hq i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_face _) (by omega)) h0))
lemma Grade.mul (h:Grade Λ U)(H:Grade Λ U'): Grade Λ (fun x=> U x* U' x):= by
 obtain ⟨c,k,h,H'⟩:=h; obtain ⟨d,l,h0,hq⟩:=H; refine ⟨c*d,k+l,mul_nonneg h h0,fun i=>⟨mul_nonneg (H' i).1 (hq i).1,?_⟩⟩; rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (H' i).2 (hq i).2 (hq i).1 ((H' i).1.trans (H' i).2)
lemma Grade.raise (h: Grade Λ U)(k:ℕ): Grade Λ (fun x=> U x^k) := by induction k with
 | zero=> simp_rw [pow_zero]; exact gia _ zero_le_one
 | succ k ih=> simp_rw [pow_succ]; exact ih.mul h
lemma Grade.down (h:Grade Λ U)(H:U'≤ U)(hh:∀ x,0≤U' x):Grade Λ U':= by obtain ⟨a,k,h,h'⟩:=h; exact ⟨a,k,h,fun x=>⟨hh x,(H x).trans (h' x).2⟩⟩
lemma Grade.sum {ι:Type*}(s:Finset ι){U:ι→V→ℝ}(H:∀ i∈s,Grade Λ (U i)): Grade Λ (fun x=>∑ i∈s,U i x):= by
 induction s using Finset.induction_on with | empty=> simp only [sum_empty]; exact gia _ le_rfl | insert i s h hs=> simp_rw [sum_insert h]; exact (H i (mem_insert_self ..)).add (hs (fun i hi=> H i (mem_insert_of_mem hi)))

variable (Λ)
def Pay (U: V→Side→ℝ):Prop:=∃ f,Grade Λ f∧∃ k:ℕ,∀ i n,0≤ U i n ∧ U i n≤ f i*(n.val:ℝ)^k
variable {Λ}{f g: V→Side→ℝ}
lemma Pay.nonneg (H:Pay Λ f)(u:V)(n:Side):0≤f u n:=by obtain ⟨_,_,_,h⟩:= H; exact (h _ _).1
lemma Pay.lift {f:V→ℝ}(h:Grade Λ f):Pay Λ (fun i _=> f i):= ⟨f,h,0,fun i n=>⟨h.nonneg i,(by simp)⟩⟩
lemma Pay.length (Λ: V→ℝ):Pay Λ (fun _ n=> (n.val:ℝ)):= ⟨_,gia _ zero_le_one,1,fun i n=>⟨by positivity,by simp⟩⟩
lemma Days (n:Side): (1:ℝ)≤n.val:= by exact_mod_cast (n.pos : 1≤n.val)
lemma Pay.stamp (h:Pay Λ f)(H:Pay Λ g): Pay Λ (fun i n=> f i n +g i n):= by
 obtain ⟨f',hf,k,h⟩:=h; obtain ⟨g',hg,l,H⟩:=H; refine ⟨_,hf.add hg,k+l,fun i n=>⟨add_nonneg (h i n).1 (H i n).1,?_⟩⟩; rw [add_mul]; exact add_le_add ((h i n).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Days _) (by omega)) (hf.nonneg i))) ((H i n).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Days _) (by omega)) (hg.nonneg i)))
lemma Pay.times (h:Pay Λ f)(H:Pay Λ g): Pay Λ (fun i n=> f i n*g i n):= by
 obtain ⟨f',hf,k,h⟩:=h; obtain ⟨g',hg,l,H⟩:=H; refine ⟨_,hf.mul hg,k+l,fun i n=>⟨mul_nonneg (h i n).1 (H i n).1,?_⟩⟩; rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (h i n).2 (H i n).2 (H i n).1 ((h i n).1.trans (h i n).2)
lemma Pay.raise (h:Pay Λ f)(k:ℕ):Pay Λ (fun i n=> f i n^k):= by induction k with
 | zero=> simp only [pow_zero]; exact Pay.lift (gia (Λ:=Λ) _ zero_le_one)
 | succ k ih=> simp only [pow_succ]; exact Pay.times ih h
lemma Pay.fixed (Λ:V→ℝ)(k:ℝ)(h:0≤k):Pay Λ (fun _ _=>k):= Pay.lift (gia _ h)
lemma Pay.low (Λ:V→ℝ): Pay Λ (fun _ n=> (Fintype.card (Site n):ℝ)):= by simp_rw [site_card,Nat.cast_pow]; exact (Pay.length Λ).raise _
lemma Pay.grid (α:Type)[Fintype α](Λ:V→ℝ) : Pay Λ (fun _ n=> (Fintype.card (Leaf n α):ℝ)):= by unfold Leaf; simp only [Fintype.card_prod,Nat.cast_mul]; exact (Pay.low Λ).times (Pay.fixed Λ _ (by positivity))
lemma Pay.sum {ι:Type*}(s:Finset ι){f:ι→V→Side→ℝ}(h:∀ i∈s,Pay Λ (f i)):Pay Λ (fun i n=> ∑ j∈s,f j i n) := by induction s using Finset.induction_on with | empty=> simp only [sum_empty]; exact Pay.fixed _ _ le_rfl | insert i s hh hs=> simp_rw [sum_insert hh]; exact (h i (mem_insert_self ..)).stamp (hs (fun j ht=> h j (mem_insert_of_mem ht)))
end Money
end YM.AllOrder.Ink
