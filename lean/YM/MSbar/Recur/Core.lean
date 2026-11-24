import YM.MSbar.Recur.Pale
/-! Recursion skeleton. All eps real/fictitious entries stored (values outside scheme open
region never used). All horizon vertices include pure vacuum const (for Lap closure);
compute normalizing constants separately (don't insert into phase tests).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open scoped Classical Topology BigOperators
variable {C:Type}(W:Edition C)
structure Pulse where
    P : Sites C
    law : SizeLaw C
    width : ℝ
    pay : Window W 0 width P
    light : Pale.Light P
    seed : ℕ → Vertex C -- bare vertices any dimensions, coupling positive, no ℏ
    start : seed 0=0
    calm(k:ℕ) : Live W 0 (seed k)
    hom(k:ℕ) : Scale.tick (Scale.mass law 0 0) (seed k)=0
variable {W} {k n i:ℕ}{d:Bit}{A:Poly W 0 0 d}
abbrev ListV(C: Type) := Category.Epoch.Whole (Film C)
variable {F G:ListV C} {g:Film C}(X:Pulse W)
-- shunts
def tripped (A:Mono W 0 d)(f:ℕ→Film C): ℕ→Film C
    | 0=> 0
    | n+1=> delay A (f n)
def seek (A: Poly W 0 0 d)(F G:ListV C)(k n:ℕ):= ∑ i∈Finset.antidiagonal k, ∑ j∈ Finset.antidiagonal n, make A (F i.1 j.1) (G i.2 j.2)
@[simp] lemma make_nil {F:Film C}: make A 0 F=0:=by funext n; unfold make; simp
@[simp] lemma make_rnil {F:Film C}: make A F 0=0:=by funext n; unfold make; simp
-- ensures score S depends on k+n−1 when predecessor F0=0
def Score (F:ListV C)(k n :ℕ): Film C:= tripped (Work.loop X.pay (show (0:Bit)=_ from (add_zero _).symm)) (F k) n + (-(2:ℂ)⁻¹) • seek (Work.tree X.pay (show (0:Bit)=_ from (by simp : (0:Bit)=0+0+0))) F F k n
lemma price_only (hu:F 0=0)(hf:G 0=0)(he:∀ i j:ℕ,i+j<k+n→ F i j=G i j): Score X F k n= Score X G k n:=by
   unfold Score; apply congr_arg₂ (·+·)
   · cases n with | zero=>rfl | succ n=>rw [tripped,tripped,he k n (by omega)]
   apply congr_arg; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
   have hn:= Finset.mem_antidiagonal.mp hi; have h:= Finset.mem_antidiagonal.mp hj; by_cases h1:i.1=0; simp [h1,hu,hf]; by_cases h2:i.2=0; simp [h2,hf,hu]; rw [he i.1 j.1 (by omega),he i.2 j.2 (by omega)]

-- solve each column, then MS subtract. outside hood deterministic undefined values via total extension
-- save degree-zero bare at ℓ=n=0
-- get label for epoch
abbrev head (X:Pulse W)(k n i:ℕ): Functionals C:= if n=0 ∧ i=0 then liftV (X.seed k) else 0
def tabs (F:Film C)(k n:ℕ)(i:ℕ) : Functionals C:= if i≤n then fun z=> solve (Scale.mass X.law i z) (cap X.law) (F i z)+head X k n i z else 0
def prepare (F:ListV C) (k n:ℕ):= Counter.clean (hood n) W 0 (scope n) (tabs X (Score X F k n) k n)
-- well-founded recursion can carry F proxy
-- use approximate iteration (simultaneous iterate) so branch proof pointwise no well-founded rec elaboration
-- still deterministic at every total order
private def march : ℕ→ListV C
    | 0=> 0
    | n+1=> fun k v=> if k=0 then 0 else prepare X (march n) k v
def evolve : ListV C:= fun k v=>march X (k+v+1) k v
private lemma march_zero (n:ℕ): march X n 0=0:=by cases n; rfl; funext v; simp [march]
private lemma march_same (k n:ℕ)(i j:ℕ) (he:k+n+1≤ i)(hf:k+n+1≤j): march X i k n=march X j k n:= by
   induction i generalizing k n j with
   | zero=> omega
   | succ i ih=> cases j with | zero=>omega | succ j=> rw [march,march]; dsimp only; split_ifs; rfl; unfold prepare; rw [price_only X (march_zero X _) (march_zero X _) (fun u v hn=> ih u v j (by omega) (by omega))]
@[simp] lemma initial : evolve X 0=0:=by funext v; simp [evolve,march_zero]
lemma grow (hv:0<k): evolve X k n=prepare X (evolve X) k n := by
    have hh : k≠0:= Nat.ne_of_gt hv; rw [evolve,march]; dsimp only; rw [if_neg hh, prepare,price_only X (march_zero X _) (initial X) ?_]; rfl
    intro i j h; unfold evolve; apply march_same; omega; omega -- apply on evolved d
end YM.MSbar.Play.Produce
