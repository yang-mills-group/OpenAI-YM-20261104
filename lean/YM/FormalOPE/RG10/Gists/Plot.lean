import YM.FormalOPE.RG10.Gists.Atoms
/-!
 # Exponential via partitions on generalized Heat family
 Pointwise in assigned gauge variables and positions, suppress external stub profile-dependent
 budgets. This is precisely Exp and Log of this term (after zero vac normalization).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gists
-- world ordinary from hot log spectra
open Function PowerSeries Marker Finset RG10.Word Gists.Word Route
open Multi (parts substitute shards Hot unionOf)
open scoped Topology BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {I:Type}
variable (R:Census V)
namespace Word
variable (m: V→ Series) (S : Finset V)
abbrev spark (v:V) := sing (R.fire v) (m v)
omit [Fintype V] in
lemma ended : vac R (∑ i∈ S,spark R m i)=0:= by rw [map_sum]; exact sum_eq_zero (fun i _=> hot_off (Multi.Hot.one R i) (m i))
lemma sparkling : expMark (∑ i∈ S,spark R m i)=∏ i∈ S,(1+spark R m i):= by
 induction S using Finset.induction_on with
 | empty=> rw [sum_empty,prod_empty,← show logWord (R:=R) 1=0 from log_one, exp_log]; simp
 | insert i S he ih=> rw [sum_insert he,prod_insert he,exp_add _ _ (show vac R (spark R m i)=0 from hot_off (Multi.Hot.one R i) (m i)) (ended ..),ih,show expMark (spark R m i) =1+spark R m i from launched (Multi.Hot.one R i) (m i)]
lemma by_atoms : emit R m=expMark (∑ i,spark R m i):= Eq.symm (sparkling R m univ)
end Word
variable (B: R.Mode→Channel I) (f: Hot R → Channel I)
-- Permit any Eval-body values at arbitrary root tuple or fixed tests depending on point.Reoccup

def program (f : Hot R →Channel I) (s:R.Mode):Channel I:=∑ j∈shards R s,∏ x∈j.val,f x
omit [Fintype V] in
@[simp] lemma blank : program R f R.quiet=1:= by rw [program,Multi.shards_quiet, Finset.sum_singleton]; rfl -- careful unfold before
-- Word views

def dramatize (y:I→ℂ) : Word R:= ∑ x: Hot R,sing x.val (run y (f x))
def seeOrd (y:I→ℂ) : Word R:= RG10.Word.package (fun s:R.Mode=> run y (B s))
variable (u:I→ℂ)
omit [Fintype V] in
lemma seen (s:R.Mode): RG10.Word.see s (seeOrd R B u)=run u (B s):= see_package ..
omit [Fintype V] in
lemma sees (s: Hot R): RG10.Word.see s.val (dramatize R f u)=run u (f s):= by
 rw [dramatize, see_sum,sum_eq_single s]; · simp
 · intro x hx hh; rw [see_sing, if_neg (fun H=>hh (Subtype.ext H.symm))]
 simp
omit [Fintype V] in
lemma under : RG10.Word.vac R (dramatize R f u)=0:= by unfold dramatize; rw [map_sum]; exact sum_eq_zero fun i _=> hot_off i _

lemma plotting : RG10.Word.expMark (dramatize R f u)=seeOrd R (program R f) u:= by
 let p x:= run u (f x); let Q:=∑ i:Hot R, Word.spark (parts R) p i; have he : dramatize R f u= parcel R Q:= by
    unfold Q dramatize; rw [map_sum]; apply sum_congr rfl; intro i _; rw [Word.spark, pitch, Multi.unionOf_single]
 rw [he,←expense Q (Word.ended (parts R) p univ), ←show emit (parts R) p=expMark Q from Word.by_atoms (parts R) p]; apply observe_ext; intro s
 simp_rw [parcels,seen,program, _root_.map_sum, emit_part, _root_.map_prod]; rfl
end YM.FormalOPE.RG10.Gists
