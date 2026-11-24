import YM.AllOrder.Ink.Money
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M l:ℕ} {a C D b:ℝ}
namespace Money
-- arbitrary Λ (order priced; can depend on sign cut by gate anyway)
variable {V : Type} (Λ:V→ℝ)
def CreditF (k:ℕ) (U:V→ℝ): Prop:=∃ a:ℝ,0≤a ∧ ∀ u, 0≤U u∧U u≤a*(1+|Λ u|)^k
variable {Λ} {U U':V→ℝ}
lemma CreditF.nonneg (h:CreditF Λ k U)(u:V):0 ≤ U u:= by obtain ⟨c,h,h'⟩:=h; exact (h' u).1
lemma freeC {Λ: V→ℝ} (b:ℝ)(hb:0≤b):CreditF Λ 0 (fun _=>b):= ⟨b,hb,fun _=>⟨hb,by simp⟩⟩
lemma givenC (h:∀ x,0≤Λ x):CreditF Λ 1 Λ:=⟨1,zero_le_one,fun x=>⟨h x,(by simp; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))⟩⟩
lemma CreditF.up (h:CreditF Λ k U)(hc:k≤l) : CreditF Λ l U:= by obtain ⟨a,h,hx⟩:=h; exact ⟨a,h,fun i=>⟨(hx i).1,(hx i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_face _) hc) h)⟩⟩
lemma CreditF.add (h:CreditF Λ k U)(H:CreditF Λ k U'): CreditF Λ k (fun x=> U x+ U' x):= by
 obtain ⟨c,h,H'⟩:=h; obtain ⟨d,h0,hq⟩:=H; refine ⟨c+d,add_nonneg h h0,fun i=>⟨add_nonneg (H' i).1 (hq i).1,?_⟩⟩; rw [add_mul]; exact add_le_add ((H' i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_face _) (by omega)) h)) ((hq i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_face _) (by omega)) h0))
lemma CreditF.mul (h:CreditF Λ k U)(H:CreditF Λ l U'): CreditF Λ (k+l) (fun x=> U x* U' x):= by
 obtain ⟨c,h,H'⟩:=h; obtain ⟨d,h0,hq⟩:=H; refine ⟨c*d,mul_nonneg h h0,fun i=>⟨mul_nonneg (H' i).1 (hq i).1,?_⟩⟩; rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (H' i).2 (hq i).2 (hq i).1 ((H' i).1.trans (H' i).2)
lemma CreditF.raise (h: CreditF Λ l U)(k:ℕ): CreditF Λ (l*k) (fun x=> U x^k) := by induction k with
 | zero=> simp_rw [pow_zero,Nat.mul_zero]; exact freeC _ zero_le_one
 | succ k ih=> simp_rw [pow_succ]; rw [Nat.mul_succ]; exact ih.mul h
lemma CreditF.down (h:CreditF Λ k U)(H:U'≤ U)(hh:∀ x,0≤U' x):CreditF Λ k U':= by obtain ⟨a,h,h'⟩:=h; exact ⟨a,h,fun x=>⟨hh x,(H x).trans (h' x).2⟩⟩
lemma CreditF.sum {ι:Type*}(s:Finset ι){U:ι→V→ℝ}(H:∀ i∈s,CreditF Λ k (U i)): CreditF Λ k (fun x=>∑ i∈s,U i x):= by
 induction s using Finset.induction_on with | empty=> simp only [sum_empty]; exact (freeC _ le_rfl).up (Nat.zero_le _) | insert i s h hs=> simp_rw [sum_insert h]; exact (H i (mem_insert_self ..)).add (hs (fun i hi=> H i (mem_insert_of_mem hi)))

variable (Λ)
def Weight (k:ℕ) (U: V→Side→ℝ):Prop:=∃ f,CreditF Λ k f∧∀ i n,0≤ U i n ∧ U i n≤ f i*(n.val:ℝ)^k
variable {Λ}{f g: V→Side→ℝ}
lemma Weight.nonneg (H:Weight Λ k f)(u:V)(n:Side):0≤f u n:=by obtain ⟨_,_,h⟩:= H; exact (h _ _).1
lemma Weight.lift {f:V→ℝ}(h:CreditF Λ k f):Weight Λ k (fun i _=> f i):= ⟨f,h,fun i n=>⟨h.nonneg i,(by exact le_mul_of_one_le_right (h.nonneg i) (one_le_pow₀ (Days n)))⟩⟩
lemma Weight.length (Λ: V→ℝ):Weight Λ 1 (fun _ n=> (n.val:ℝ)):= ⟨_,(freeC _ zero_le_one).up zero_le_one,fun i n=>⟨by positivity,by simp⟩⟩
lemma Weight.ups (h:Weight Λ k f)(he:k≤l):Weight Λ l f:= by obtain ⟨g,h,hx⟩:=h; exact ⟨g,h.up he, fun i n=>⟨(hx i n).1, (hx i n).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Days n) he) (h.nonneg i))⟩⟩
lemma Weight.stamp (h:Weight Λ k f)(H:Weight Λ k g): Weight Λ k (fun i n=> f i n +g i n):= by
 obtain ⟨f',hf,h⟩:=h; obtain ⟨g',hg,H⟩:=H; refine ⟨_,hf.add hg,fun i n=>⟨add_nonneg (h i n).1 (H i n).1,?_⟩⟩; rw [add_mul]; exact add_le_add ((h i n).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Days _) (by omega)) (hf.nonneg i))) ((H i n).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Days _) (by omega)) (hg.nonneg i)))
lemma Weight.times (h:Weight Λ k f)(H:Weight Λ l g): Weight Λ (k+l) (fun i n=> f i n*g i n):= by
 obtain ⟨f',hf,h⟩:=h; obtain ⟨g',hg,H⟩:=H; refine ⟨_,hf.mul hg,fun i n=>⟨mul_nonneg (h i n).1 (H i n).1,?_⟩⟩; rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (h i n).2 (H i n).2 (H i n).1 ((h i n).1.trans (h i n).2)
lemma Weight.raise (h:Weight Λ l f)(k:ℕ):Weight Λ (l*k) (fun i n=> f i n^k):= by induction k with
 | zero=> simp only [pow_zero,Nat.mul_zero]; exact Weight.lift (freeC (Λ:=Λ) _ zero_le_one)
 | succ k ih=> simp only [pow_succ]; rw [Nat.mul_succ]; exact Weight.times ih h
lemma Weight.fixed (Λ:V→ℝ)(k:ℝ)(h:0≤k):Weight Λ 0 (fun _ _=>k):= Weight.lift (freeC _ h)
lemma Weight.low (Λ:V→ℝ): Weight Λ 4 (fun _ n=> (Fintype.card (Site n):ℝ)):= by simp_rw [site_card,Nat.cast_pow]; simpa only [Nat.one_mul] using (Weight.length Λ).raise 4
lemma Weight.grid (α:Type)[Fintype α](Λ:V→ℝ) : Weight Λ 4 (fun _ n=> (Fintype.card (Leaf n α):ℝ)):= by unfold Leaf; simp only [Fintype.card_prod,Nat.cast_mul]; exact (Weight.low Λ).times (Weight.fixed Λ _ (by positivity))
lemma Weight.sum {ι:Type*}(s:Finset ι){f:ι→V→Side→ℝ}(h:∀ i∈s,Weight Λ k (f i)):Weight Λ k (fun i n=> ∑ j∈s,f j i n) := by induction s using Finset.induction_on with | empty=> simp only [sum_empty]; exact (Weight.fixed _ _ le_rfl).ups (Nat.zero_le _) | insert i s hh hs=> simp_rw [sum_insert hh]; exact (h i (mem_insert_self ..)).stamp (hs (fun j ht=> h j (mem_insert_of_mem ht)))
lemma CreditF.grade (h:CreditF Λ k U):Grade Λ U := by obtain ⟨a,h,hx⟩:=h; exact ⟨a,k,h,hx⟩
lemma Weight.grade (h:Weight Λ k f):Pay Λ f:=by obtain ⟨g,h,hx⟩:=h; exact ⟨g,h.grade,k,hx⟩
end Money
end YM.AllOrder.Ink

