import YM.MSbar.Series.Delta
/-! Epoch external index. Work first k = total source-and-positive-coupling order, then
n = full ℏ; all indices are bounded at each invocation. No empty graph term. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category.Epoch
open Calculus Twist Function Finset Filter
open scoped BigOperators Classical
variable {X Y Z: Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z]
-- groups Point = loops (`ℕ`), Over = coupling. Works with X as Phase all ℓ as well
abbrev Whole (X:Type*) := Form (Form X)
variable {A:Homo X X}{B:Homo Y Y}{M:Machine X Y}
def grow (M:Machine X Y): Machine (Whole X) (Whole Y):= propagate (propagate M true) false
def elevate (A:Homo X X):= act (act A)
lemma stretch_zero(A:Homo X X): Twist.stretch A 0=act A:= by ext f n; simp [Twist.stretch,Twist.nel]
lemma principle (h: Calculus M)(H:Twist M A B 0): Twist (grow M) (elevate A) (elevate B) 0:=by
   simpa only [grow,elevate,Bool.false_eq_true,↓reduceIte, Twist.nel,stretch_zero, sub_zero] using Twist.next (Calculus.next h true) (Twist.next h H true 0) false 0
variable {S U: Whole X}{k n:ℕ}
abbrev Cone {X:Type*}[Zero X](k n:ℕ)(a:Whole X):Prop := ∀ i≤k,∀ j≤n,a i j=0
-- annihilates error-supported sweeps
lemma push (h: Cone k n S) (B:Homo X Y) (s:Bool): (act (post s B) S) k n=0:=by
    cases s with
    | false=> simp [post,h _ le_rfl n le_rfl]
    | true=> cases n <;> first | exact rfl | simp [post,h _ le_rfl _ (show _ ≤ _ from Nat.le_succ _)]
lemma product (h:Cone k n S)(B: Tree Y X Z)(g:Whole Y) : knot (knot B) g S k n=0:=by
    simp only [knotted,Finset.sum_apply];apply sum_eq_zero; intro a ha; apply sum_eq_zero; intro b hb; rw [h _ (by have := (Finset.mem_antidiagonal.mp ha); have := (Finset.mem_antidiagonal.mp hb); omega) _ (by have := (Finset.mem_antidiagonal.mp ha); have := (Finset.mem_antidiagonal.mp hb); omega),map_zero]
lemma eras (A:Tree X Y Z)(g:Whole Y)(E:S 0=0)(K:∀ i<k,∀ j≤n,g i j=0): knot (knot A) S g k n=0:= by
    simp only [knotted,Finset.sum_apply]; apply sum_eq_zero; rintro ⟨b,c⟩ H; apply sum_eq_zero; intro u hu; have hx:b+c=k:= mem_antidiagonal.mp H; dsimp; rcases eq_or_ne b 0 with rfl|hb; simp [E]; rw [K _ (by omega) _ (by have := (Finset.mem_antidiagonal.mp hu); omega),map_zero]
lemma timer (E:∀ i<n,S k i=0) (B:Homo X Y): act (sea B) S k n=0:=by
    cases n; simp; simp [E _ (Nat.lt_succ_self _)]
lemma anomaly_zero (HS:S 0=0): anomaly (grow M) S 0=0:=by
    unfold anomaly; simp only [grow,propagate,post,Bool.false_eq_true,↓reduceIte,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,act_val]; simp [HS]
lemma rigidity (h:Calculus M)(H: Twist M A B 0)(E: S 0=0)(hs:Cone k n (elevate A S - current (grow M) S))
    (he:∀ i<n,anomaly (grow M) S k i=0) (hj:∀ i<k,∀ j≤n,anomaly (grow M) S i j=0):
    B (anomaly (grow M) S k n)=0:=by
    let x:= anomaly (grow M) S;let s:= elevate A S-current (grow M) S
    have hh := congr_fun (congr_fun (Calculus.alive (Calculus.next (Calculus.next h true) false) (principle h H) S) k) n
    change B (x k n)= _- knot (knot M.mix) S x k n + _ at hh; change B (x k n)=0
    have hU: update (grow M) S s k n=0:=by
        change act (act M.brst) s k n + knot (knot M.bracket) S s k n - act (sea M.red) s k n=0
        rw [show act (act M.brst) s k n=0 from push hs _ false,show act (sea M.red) s k n=0 from push hs _ true,product hs]; simp
    rw [hh]; change act (sea M.blue) x k n- _+ update (grow M) S s k n=0; rw [timer (S:=x) (fun i hi=>(he i hi)), hU,eras M.mix x E hj]; simp
end YM.MSbar.Category.Epoch
