import YM.MS.Book.Pairs
import YM.MS.Book.Ranks
import Mathlib.Data.Nat.Pairing
/-! antidiagonal bookkeeping for formal expansions.
 Work with `ℕ→ V` linear, weight rings only per constants.
 triple reordering avoiding inconvenient sigma eqs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Convolve
open Function Filter Set Finset Koszul
variable {A E F X Y Z : Type*}
variable [CommRing A][AddCommGroup E][Module A E][AddCommGroup F][Module A F][AddCommGroup X][Module A X]

variable (L:E→ₗ[A] F→ₗ[A] X)

def pairW (L:E→ₗ[A] F→ₗ[A] X):T E→ₗ[A] T F→ₗ[A] T X where
   toFun u:= {toFun v:= fun n=>∑ d∈antidiagonal n,L (u d.1) (v d.2)
              map_add' x y:= by ext n; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
              map_smul' c x:= by ext n; simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply] }
   map_add' x y:= by ext1 k; ext n; change ∑ d∈antidiagonal n,L ((x+y) d.1) (k d.2)= (∑ d∈antidiagonal n,L (x d.1) (k d.2)) + ∑ d∈antidiagonal n,L (y d.1) (k d.2); simp_rw [Pi.add_apply,map_add,LinearMap.add_apply,Finset.sum_add_distrib]
   map_smul' c x:= by ext1 k; ext n; change ∑ d∈antidiagonal n,L ((c • x) d.1) (k d.2)= c • ∑ d∈antidiagonal n,L (x d.1) (k d.2); simp_rw [Pi.smul_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum]
lemma paired (u:T E) (v:T F) n: pairW L u v n=∑ d∈antidiagonal n,L (u d.1) (v d.2):= rfl
lemma flips (u:T E)(v:T F): pairW L u v=pairW (L.flip) v u:= by ext n; rw [paired,paired]; exact Finset.Nat.sum_antidiagonal_swap (f:=fun d=>L (u d.2) (v d.1)) -- namespace

def promote (L:E→ₗ[A] F) : T E→ₗ[A] T F:= {
   toFun u n:= L (u n)
   map_add' _ _:= by ext; simp
   map_smul' _ _:= by ext; simp }
lemma promised (L:E→ₗ[A] F) (F:T E)(n:ℕ): promote L F n=L (F n):= rfl

variable [AddCommMonoid Y]
end YM.MS.Book.Convolve
