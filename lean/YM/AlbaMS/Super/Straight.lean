import YM.AlbaMS.Super.Porch

/-!
# Wick, linear commutator, exponential conjugation

Only identity at actual finite profiles used here. Powers kill on finite
ranks; linear transport across a band allowed for arbitrary finite stages,
with graded master calc only at endpoints. Do not assume real Nielsen identities
for the physical expectations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function IsNilpotent
open scoped BigOperators Classical
variable {ι R : Type*} [CommRing R] [Algebra ℚ R] {ρ : ι→Bool}
variable {F G I : Coil ρ R} {k g K : ι→ι→R} {s : Finset ι} {m n : ℕ} {W U A : Module.End R (Coil ρ R)}

/-- linear intertwining with possible commutator that itself commutes. -/
def reflects (U A : Module.End R (Coil ρ R))(k : ι→ι→R)(s : Finset ι):=∀ F, U (touch k s F)= touch k s (U F)+ A F
omit [Algebra ℚ R] in
lemma reflects_power (h:reflects U A k s)(H:Commute A (touch k s)):
    U ((touch k s ^ (n+1)) F)=(touch k s ^(n+1)) (U F) + ((n+1:ℕ):R) • A ((touch k s^n) F):=by
  have he F : touch k s (A F)= A (touch k s F):= LinearMap.congr_fun H.symm F
  induction n with
  | zero=>simp; exact h _
  | succ n ih=>
    rw [pow_succ' _ (n+1),Module.End.mul_apply,Module.End.mul_apply,h,ih,map_add,map_smul]
    rw [he, ← Module.End.mul_apply (touch k s) (touch k s ^ n) F, ← pow_succ' (touch k s) n, Nat.cast_add (R:=R) (n+1),Nat.cast_one,add_smul,one_smul,add_assoc]
lemma reflects_pe (h:reflects U A k s)(H:Commute A (touch k s)): U (pe k s (n+1) F)=pe k s (n+1) (U F)+ A (pe k s n F):=by
  simp_rw [pe_apply,map_smul]; rw [reflects_power h H,smul_add,smul_smul,mul_comm (falt R (n+1)),falt_succ]
lemma reflects_twig (h:reflects U A k s)(H:Commute A (touch k s)): U (twig k s (n+1) F)=twig k s (n+1) (U F)+ A (twig k s n F):=by
  rw [twig_apply,twig_apply,twig_apply,Finset.sum_range_succ',Finset.sum_range_succ' _ (n+1),map_add,pe_zero,pe_zero,map_sum,map_sum]; simp_rw [reflects_pe h H,Finset.sum_add_distrib]; abel
lemma reflects_wither (h:reflects U A k s)(H:Commute A (touch k s))(tv:FinRank F)(hv:FinRank (U F)): U (wither k s F)=wither k s (U F)+ A (wither k s F):=by
  let n := max tv.choose hv.choose; rw [withers hv.choose_spec (by omega : hv.choose ≤ 2*(n+1))]; nth_rw 1 [withers tv.choose_spec (by omega : tv.choose≤ 2*(n+1))]; rw [reflects_twig h H,← withers tv.choose_spec (by omega : tv.choose ≤ 2*n)]

-- projected identities. keep Q0 as a linear map kicking. later uses finite orbits with tuned coefficients.
def master_eff (U : Coil ρ R →ₗ[R] Coil ρ R)(k:ι→ι→R)(s:Finset ι)(S : Coil ρ R) := U S + master k s S
lemma master_rule (h:Tone false F)(hr:IsNilpotent F)(hg:Graded ρ true g)(H:lever U.toAddMonoidHom):
   (U-touch g s : Module.End R (Coil ρ R)) (exp (-F))=-(exp (-F)*master_eff U g s F):=by
  simp only [LinearMap.sub_apply,master_eff,master]; -- linear coerces
  rw [show U (exp (-F)) = _ from swept H h.neg hr.neg,touch_exp h.neg hg hr.neg];
  simp only [mul_add,mul_sub,map_neg]; simp_rw [← from_tether (F:=-F), map_neg,LinearMap.neg_apply,from_tether,neg_neg]; simp; abel
lemma origin_eff {J : ι→ι→R} (hg:Graded ρ true g)(hJ:Graded ρ true J)
    (hp:reflects (U-touch g s : Module.End R (Coil ρ R)) (touch J s-touch g s) k s)(HQ:Graded ρ false k)
    (H:lever U.toAddMonoidHom) (h:Tone false F) (hv:IsNilpotent F) (he:master_eff U g s F=0)
    (hr:FinRank F)(hh:Tone false G)(hx:IsNilpotent G)(ha:exp (-G)=wither k s (exp (-F))): master_eff U J s G=0:=by
  have h0 : (U-touch g s : Module.End R (Coil ρ R)) (exp (-F))=0:=by rw [master_rule h hv hg H,he,mul_zero,neg_zero]
  have hhQ : Commute (touch J s - touch g s : Module.End R (Coil ρ R)) (touch k s):=by
    have he : ∀ M : ι → ι → R, Graded ρ true M → Commute (touch (ρ:=ρ) M s) (touch k s):= fun M hM=> LinearMap.ext fun i=> (touch_touch true false i M k s s hM HQ); exact Commute.sub_left (he _ hJ) (he _ hg)
  have hl:=(reflects_wither hp hhQ hr.neg.exponent (h0.symm ▸ FinRank.none))
  have ht : (U-touch J s : Module.End R (Coil ρ R)) (exp (-G))=0:=by
    rw [← ha,h0,wither_nil,zero_add,LinearMap.sub_apply,LinearMap.sub_apply] at hl
    apply sub_eq_zero.mpr; exact sub_left_inj.mp hl
  rw [master_rule hh hx hJ H,neg_eq_zero] at ht; exact IsUnit.mul_left_cancel (isUnit_exp hx.neg) (ht.trans (mul_zero _).symm) -- left?
end YM.MSBar.Bric.Coil
