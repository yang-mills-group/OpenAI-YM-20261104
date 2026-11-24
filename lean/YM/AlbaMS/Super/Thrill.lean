import YM.AlbaMS.Super.Banks
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Module.Submodule.Pointwise
/-!
Ordinary germs. Euler identities on finite support allow cheap induction by
linear symbols. Locale may be infinite (we keep finite **individual** supports).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R E W : Type*} [CommRing R] [AddCommMonoid W] {ρ : ι→Bool} (p q : Bool)
variable (F G H : Coil ρ R) (l : List ι) (x y : ι) (n : ℕ)
namespace Coil

def varC (R : Type*) [CommRing R] (ρ : ι→Bool)(x:ι): Coil ρ R:= ⟨fun l=> if l=[x] then 1 else 0,fun (a l : List ι) (i j)=> show ite ((a++i::j::l)=[x]) 1 0=sting (W:=R) (ρ i && ρ j) (ite ((a++j::i::l)=[x]) 1 0) from by
  cases a <;> simp⟩
lemma var_read : varC R ρ x l=if l=[x] then (1:R) else 0:=rfl
@[simp] lemma varD : D x (varC R ρ y)=if x=y then 1 else 0:=by ext l; cases l <;> by_cases h:x=y <;> simp [D_read,var_read,h]
@[simp] lemma var_nil : varC R ρ x []=0:=by simp [var_read]
lemma var_inside {s : Set ι} (h:x∈s): Inside s (varC R ρ x):=by intro l hh; rw [var_read] at hh; split at hh; subst l; simpa; exact False.elim (hh rfl)
lemma var_pure (f:ι→ W) : Pure f (f x) (varC R ρ x):= by intro l h; rw [var_read] at h; split at h; subst l; simp [weight];exact False.elim (h rfl)
lemma var_tone : Tone (ρ x) (varC R ρ x) := by intro l h; rw [var_read] at h; split at h; subst l; simp;exact False.elim (h rfl)
lemma var_cap : Cap (varC R ρ x) 1 := by intro l h; rw [var_read] at h; split at h; subst l; rfl; exact False.elim (h rfl)
def Heg (n : ℕ)(F : Coil ρ R):Prop:=∀ l,F l≠0→ l.length=n
namespace rankn
lemma tone (h:Tone p F): Tone p (rankn n F):= by intro l hv; rw [rankn_read] at hv; split at hv; exact h l hv; exact False.elim (hv rfl)
lemma inside {s} (h:Inside s F) : Inside s (rankn n F):= by intro l hv;rw [rankn_read] at hv;split at hv;exact h l hv;exact False.elim (hv rfl)
lemma heg : Heg n (rankn n F):= by intro l hv;rw [rankn_read] at hv; split at hv; assumption;exact False.elim (hv rfl)
end rankn
namespace Heg
lemma pure_iff : Heg n F ↔ Pure (fun _=> (1:ℕ)) n F:= by unfold Pure Heg; simp [weight]
lemma cap (h:Heg n F): Cap F n:= fun l hv=> (h l hv).le
variable {n F G}
lemma mul {m} (h:Heg n F)(H:Heg m G): Heg (n+m) (F*G):=by rw [pure_iff] at *;exact h.mul H
lemma D_zone (h:Heg (n+1) F): Heg n (D x F):=by
  rw [pure_iff] at *; rw [Nat.add_comm] at h; exact h.dz x
lemma add (h:Heg n F)(H:Heg n G): Heg n (F+G):=by rw [pure_iff] at *;exact h.add H
lemma sum (v:Finset E)(t:E→ Coil ρ R)(h:∀ i∈v,Heg n (t i)): Heg n (∑ i∈v,t i):= (pure_iff ..).2 (Pure.sum v t (fun i hi=> (pure_iff ..).1 (h i hi)))
lemma smul (h:Heg n F)(c:R): Heg n (c • F):= by rw [pure_iff] at *;exact h.smul c
lemma var : Heg 1 (varC R ρ x):=(pure_iff ..).2 (var_pure x _)
lemma put0 (c:R): Heg 0 (put ρ c):=(pure_iff ..).2 (Pure.const c)
lemma one : Heg 0 (1:Coil ρ R):= put0 1
lemma zero : Heg n (0:Coil ρ R):=(pure_iff ..).2 Pure.zero
lemma criterion (h:Heg n F): rankn n F=F:=by
  ext l; rw [rankn_read]; split; rfl; next he=> exact (not_not.1 (mt (h l) he)).symm
end Heg
lemma ranks (h : Cap F n) : (∑ i∈ Finset.range (n+1), rankn i F)=F:=by
  ext l; rw [sum_read]; simp_rw [rankn_read]; rw [Finset.sum_ite_eq]; split<;> first| rfl| exact (not_not.1 (fun (hv : F l≠0)=> by have H:= h l hv; simp [Nat.lt_succ_of_le H] at *)).symm

def germ (s : Finset ι) (F : Coil ρ R):=∑ i∈s,varC R ρ i * D i F
lemma germD (s : Finset ι)(h:x∈s): D x (germ s F) = D x F+germ s (D x F):=by
  unfold germ; rw [map_sum]; simp_rw [mulD,varD,ite_mul]; rw [Finset.sum_add_distrib]; simp only [one_mul,zero_mul,Finset.sum_ite_eq,h,if_true]; congr 1
  refine Finset.sum_congr rfl fun i _=> ?_; rw [(var_tone (R:=R) (ρ:=ρ) i).pl,DD (ρ:=ρ) F x i]; cases ρ x<;>cases ρ i<;> simp
lemma germ_apply (s : Finset ι)(h:Inside (s:Set ι) F): germ s F l=(l.length:R)*F l:= by
  induction l generalizing F with
  | nil=> simp [germ,sum_read]
  | cons x l ih=>
    by_cases hx:x∈ s
    · rw [← D_read, germD _ _ _ hx]; rw [plus_read, ih (D x F) (h.dz x)]; simp [D_read,add_mul,add_comm]
    have he : Inside (s:Set ι) (germ s F):= Inside.sum _ _ (fun i hi=> (var_inside _ hi).mul (h.dz _))
    rw [← D_read,he.erased hx,zero_apply, ← D_read,h.erased hx,zero_apply,mul_zero]
lemma germ_eq (s : Finset ι)(h:Inside (s:Set ι) F)(H:Heg n F): germ s F=(n:R) • F:=by
  ext l; rw [germ_apply F l s h,smul_read]; by_cases hv:F l=0; · simp [hv]
  rw [H l hv]

-- induction for any predicate closed under linear combos and left multiplication by vars. allow track support inside s.
section Field
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
variable (s : Finset ι) (U:Submodule 𝕂 (Coil ρ 𝕂))(he:1∈U)
variable (hv:∀ i∈s, ∀ a∈U, varC 𝕂 ρ i*a∈U)
include he hv
private lemma spring (n:ℕ)(a : Coil ρ 𝕂)(h:Heg n a)(H:Inside (s : Set ι) a): a∈U:=by
  induction n generalizing a with
  | zero=>
    have heq : a= (a []) • (1:Coil ρ 𝕂):=(h.cap _ _).eroded.trans (by rw [← put_smul_left,mul_one])
    exact heq ▸ (U.smul_mem _ he)
  | succ n ih=>
    have ha : germ s a∈U:= U.sum_mem (fun i hi=> hv _ hi _ (ih _ (h.D_zone i) (H.dz i)))
    rw [germ_eq _ _ _ H h] at ha
    exact (Submodule.smul_mem_iff U (show ((n+1:ℕ):𝕂)≠0 by exact_mod_cast n.succ_ne_zero) (x:=a)).1 ha
lemma saturates {a : Coil ρ 𝕂}(h:Cap a n)(H:Inside (s : Set ι) a): a∈U:=by
  rw [← ranks a n h]; exact U.sum_mem (fun i _=> spring s U he hv i (rankn i a) (rankn.heg a i) (rankn.inside a i H))
end Field
end Coil
end YM.MSBar.Bric
