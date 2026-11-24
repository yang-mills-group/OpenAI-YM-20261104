import YM.AlbaMS.Super.Journal
import Mathlib.Algebra.Algebra.Operations

/-!
Linear semigroup calculation on finite rank. No summation convention
required on ambient dimensions. Does not forget `s`. Keep path only on the
cover relation `touch`: gauge-fixing applications later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function IsNilpotent
open scoped BigOperators Classical
variable {ι R : Type*} [CommRing R] [Algebra ℚ R] {ρ : ι→Bool}
variable {F G I : Coil ρ R} {k g K : ι→ι→R} {s : Finset ι} {m n : ℕ}

lemma wither_add (ht:FinRank F)(H:FinRank G): wither k s (F+G)=wither k s F+wither k s G:=by
  let n:=max ht.choose H.choose; have ha:Cap F n:= ht.choose_spec.up (le_max_left ..); have hb:Cap G n:= H.choose_spec.up (le_max_right ..)
  have hc:n≤2*n:=by omega
  rw [withers (ha.add hb) hc, withers ha hc,withers hb hc,map_add]
lemma wither_smul (ht:FinRank F)(c:R): wither k s (c • F)=c • wither k s F:=by have he:ht.choose≤2*ht.choose:= Nat.le_mul_of_pos_left _ (by norm_num); rw [withers (ht.choose_spec.smul _) he,withers ht.choose_spec he,map_smul]
lemma Cap.withers (h: Cap F n): Cap (wither k s F) n:= by rw [Coil.withers h (by omega : n≤2*n)]; exact h.tree
lemma wither_nil : wither k s (0:Coil ρ R)=0:=by rw [withers (n:=0) Cap.zero (m:=0) (by omega),map_zero]
lemma wither_const (c:R): wither k s (put ρ c)=put ρ c:= by rw [withers (n:=0) (Cap.const c) (m:=0) (by omega),twig_apply]; simp
lemma wither_empty (ht:FinRank F): wither 0 s F=F:=by
  have he : touch 0 s=(0:Coil ρ R→ₗ[R] Coil ρ R):= LinearMap.ext fun i=>by simp [touch_apply (k:=0)]
  rw [withers ht.choose_spec (by omega : ht.choose≤2*ht.choose),twig_apply,Finset.sum_range_succ'];simp [pe_apply,he]

def Upto (ρ : ι→Bool)(n:ℕ)(R : Type*) [CommRing R]: Submodule R (Coil ρ R) where
  carrier F:= Cap F n
  zero_mem':=Cap.zero
  add_mem':= Cap.add
  smul_mem' c _ h:= Cap.smul h c

def uTouch (ρ : ι→Bool)(k : ι→ι→R)(s:Finset ι)(n:ℕ): Module.End R (Upto ρ n R) := LinearMap.restrict (touch k s) fun F h=>(Cap.touch F n k s (Cap.up (show Cap F n from h) (by omega)))
omit [Algebra ℚ R] in
lemma uto_true (i : Upto ρ n R): (((uTouch ρ k s n)^m) i).val=(touch k s^m) i.val := by -- fix parse
  induction m with | zero=> rfl | succ j ih=> rw [pow_succ', pow_succ', Module.End.mul_apply,Module.End.mul_apply,← ih];rfl
omit [Algebra ℚ R] in
lemma uto_nil : IsNilpotent (uTouch ρ k s n):=⟨n+1,LinearMap.ext fun i=> Subtype.ext ((uto_true i).trans (killed i.property (by omega)))⟩ -- syntax
lemma utopian (i : Upto ρ n R): (exp (uTouch ρ k s n) i).val=wither k s i.val := by
  have hi : uTouch ρ k s n^(n+1)=0:=LinearMap.ext fun i=> Subtype.ext ((uto_true i).trans (killed i.property (by omega)))
  rw [exp_eq_sum hi, withers (n:=n) i.property (m:=n) (by omega),twig_apply]; simp_rw [pe_apply, falt,algebraMap_smul]
  rw [LinearMap.sum_apply, Submodule.coe_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; change ((j.factorial:ℚ)⁻¹ • (((uTouch _ _ _ _)^j) i)).val= _; rw [← uto_true]; rfl
lemma composition (ha:Graded ρ false k)(hb:Graded ρ false g)(h:FinRank F): wither (k+g) s F=wither k s (wither g s F):=by
  let n:=h.choose; let A : Upto ρ n R:=⟨F,h.choose_spec⟩; let K:= uTouch ρ k s n; let G:=uTouch ρ g s n
  have hKG:uTouch ρ (k+g) s n=K+G:=LinearMap.ext (fun i=>Subtype.ext (add_touch ..))
  have he: Commute K G:= LinearMap.ext (fun i=>Subtype.ext (touch_touch _ _ _ _ _ _ _ ha hb))
  change wither _ _ A.val=wither k s (wither g s A.val)
  rw [← utopian (k:=k+g),← utopian,← utopian,hKG,exp_add_of_commute he (show IsNilpotent K from uto_nil) (show IsNilpotent G from uto_nil)];rfl
end YM.MSBar.Bric.Coil
