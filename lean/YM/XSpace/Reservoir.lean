import YM.XSpace.Posters
import YM.XSpace.Traversal

/-!
# Algebraic calculus of contractions at positions

Work with finite sets of active linear letters when continuing; no infinite
sums over slots. Also real-linearity differs from complex linearity -- take care
of that elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter Finsupp Maxwell Maxwell.Free
open Traverse MvPolynomial Next.Rank.Normal
open scoped Topology BigOperators Classical

variable {ι : Type*} {L : Finset ι} (f g : ι → ℂ)
lemma split_eq {s : Set ι} (h : EqOn f g s) {p : poly ι} (hp : p ∈ supported ℂ s): slit f p=slit g p:=
  derivation_eqOn_supported (fun i hi=> by simp [h hi]) hp
lemma split_in (s : Set ι) {p : poly ι} (h : p∈ supported ℂ s) : slit f p∈ supported ℂ s :=by
  rw [supported_eq_range_rename,AlgHom.mem_range] at h ⊢
  obtain ⟨p,rfl⟩:=h; let z (i : s): ι→₀ℂ:= single i.val 1
  use slit (Next.Rank.Normal.reads z f) p; rw [labelled, exchange_slit]

def choose_var (i : ι) (v : ℂ): ι → ℂ:= Pi.single i v
lemma chosen_eq (i : ι) (a : ℂ) : choose_var i a i=a:= Pi.single_eq_same ..
lemma chosen_ne {i j : ι} (h:j≠i) (a : ℂ) : choose_var i a j=0:= Pi.single_eq_of_ne h _
lemma selected (i : ι) (v : ℂ) : choose_var i v=v • choose_var i 1:= by
  funext x; by_cases h:x=i; subst x; simp [choose_var]; simp [choose_var,h]
lemma split_sum (f : ι → ℂ) (U : Finset ι) {p : poly ι} (hu : p ∈ supported ℂ (U:Set ι)): slit f p = ∑ i∈U,f i • slit (choose_var i 1) p:= by
  have he : slit (∑ i∈U,choose_var i (f i)) p=∑ i∈U, slit (choose_var i (f i)) p:=by
    clear hu
    induction U using Finset.induction_on with
    | empty=> simp [slit_zero]
    | insert a s ha ih=> rw [Finset.sum_insert ha, Finset.sum_insert ha,slit_linear,ih]
  rw [split_eq f (∑ i ∈ U, choose_var i (f i)) ?_ hu,he]; swap
  · intro i hi; rw [Finset.sum_apply,Finset.sum_eq_single_of_mem i hi]; simp [choose_var]; intro b _ hb; simp [choose_var,Pi.single_eq_of_ne hb.symm]
  apply Finset.sum_congr rfl; intro i _; rw [selected i (f i),slit_smul]

lemma varied_splits (S : ℝ→ι→ℂ) {U : Set ι} (h : ∀ a∈U,Landing (fun t=> S t a) (f a)) {p : poly ι} (hp : p∈ supported ℂ U)
    (A : ℝ → (poly ι →ₗ[ℂ] ℂ)) (B : poly ι→ₗ[ℂ] ℂ) (he : ∀ p∈supported ℂ U,Landing (fun t=> A t p) (B p)) :
    Landing (fun t=> A t (slit (S t) p)) (B (slit f p)) :=by
  rw [split_sum f _ p.mem_supported_vars]; conv => lhs; intro t; rw [split_sum (S t) _ p.mem_supported_vars]
  simp_rw [_root_.map_sum,map_smul,smul_eq_mul]
  apply landed_sum; intro i hi; exact (h i (mem_supported.mp hp hi)).mul (he _ (split_in _ _ hp))

abbrev first (Q : Symmetric ι) (i : ι) (p : poly ι) := slit (Q.cov i) p
lemma stationed (Q : Symmetric ι) (i : ι) (p : poly ι) : Next.Rank.Normal.blend Q 0 (X i*p)=Next.Rank.Normal.blend Q 0 (first Q i p):=by rw [Next.Rank.Normal.blended]; simp
lemma split_leibniz (f : ι→ℂ) (p q : poly ι) : slit f (p*q)=slit f p*q+p*slit f q:=by rw [Derivation.leibniz]; simp only [smul_eq_mul]; ring

variable {G : Gauge}
def Room (G : Gauge) (S : Finset E4) : Subalgebra ℂ (Pol G):= supported ℂ (Prod.fst ⁻¹' (S : Set E4))
lemma simple_room {a : E4} (p : poly (Paint G)) {S : Finset E4} (h : a∈S): post a p∈ Room G S:=by
  induction p using MvPolynomial.induction_on with
  | C c => rw [post_C]; exact Subalgebra.algebraMap_mem ..
  | add p q hp hq => rw [_root_.map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => rw [map_mul,post_X]; exact Subalgebra.mul_mem _ hp (X_mem_supported.mpr h)
lemma room_grew {S L : Finset E4} (h : S ⊆ L) : Room G S ≤ Room G L:= supported_mono (fun _ hi=> h hi)
lemma room_after {S : Finset E4} (x : E4): Room G S ≤ Room G (insert x S):= room_grew (Finset.subset_insert ..)

def dot (p : Flavor 0) (c : G.ColorIndex): Paint G := (⟨0,p⟩,c)
def lit (x : E4) (p : Flavor 0) (c : G.ColorIndex): World G:=(x,dot p c)
def quad (p : Flavor 0): poly (Paint G):= ∑ c:G.ColorIndex, X (dot p c)* X (dot p c)
lemma quad_team (p : Flavor 0): send (quad p)=team G p p:=by unfold quad; simp_rw [_root_.map_sum,map_mul,sends]; rfl
abbrev Ph := E4 × Flavor 0

def bilocal (G : Gauge) (x y : Ph): Pol G:= ∑ a:G.ColorIndex,X (lit x.1 x.2 a) * X (lit y.1 y.2 a)
lemma quad_play (x : E4) (p : Flavor 0): post x (quad (G:=G) p)=bilocal G (x,p) (x,p):=by unfold quad; simp_rw [_root_.map_sum,map_mul,post_X]; rfl
lemma bilocal_on {s:Finset E4} (x y : Ph) (h:x.1∈s) (ht:y.1∈s): bilocal G x y ∈ Room G s:= Subalgebra.sum_mem _ fun _ _=>Subalgebra.mul_mem _ (X_mem_supported.mpr h) (X_mem_supported.mpr ht)
lemma bi_swap (x y : Ph): bilocal G x y = bilocal G y x:= Finset.sum_congr rfl fun _ _=>mul_comm ..

end YM.XSpace.Legs
